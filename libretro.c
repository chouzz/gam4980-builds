#include <stdarg.h>
#include <stdio.h>
#include <string.h>
#include "libretro.h"
#include "vrEmu6502.c"

#define _DATA1          0x00
#define _DATA2          0x01
#define _DATA3          0x02
#define _DATA4          0x03
#define _ISR            0x04
#define _TISR           0x05
#define _BK_SEL         0x0c
#define _BK_ADRL        0x0d
#define _BK_ADRH        0x0e
#define _IRCNT          0x1b
#define __addr_reg      0x26
#define _SYSCON         0x200
#define _INCR           0x207
#define _ADDR1L         0x208
#define _ADDR1M         0x209
#define _ADDR1H         0x20a
#define _ADDR2L         0x20b
#define _ADDR2M         0x20c
#define _ADDR2H         0x20d
#define _ADDR3L         0x20e
#define _ADDR3M         0x20f
#define _ADDR3H         0x210
#define _ADDR4L         0x211
#define _ADDR4M         0x212
#define _ADDR4H         0x213
#define _PB             0x21b
#define _STCON          0x226
#define _ST1LD          0x227
#define _ST2LD          0x228
#define _ST3LD          0x229
#define _ST4LD          0x22a
#define _STCTCON        0x22e
#define _CTLD           0x22f
#define _ALMMIN         0x230
#define _ALMHR          0x231
#define _ALMDAYL        0x232
#define _ALMDAYH        0x233
#define _RTCSEC         0x234
#define _RTCMIN         0x235
#define _RTCHR          0x236
#define _RTCDAYL        0x237
#define _RTCDAYH        0x238
#define _IER            0x23a
#define _TIER           0x23b
#define _AUDCON         0x23f
#define _KEYCODE        0x24e
#define _MACCTL         0x260

#define LCD_WIDTH 159
#define LCD_HEIGHT 96

static struct {
    VrEmu6502   *cpu;
    uint8_t      ram[0x8000];
    uint8_t      flash[0x200000];
    uint8_t      flash_cmd;
    uint8_t      flash_cycles;
    uint8_t      rom_8[0x200000];       /* font rom */
    uint8_t      rom_e[0x200000];       /* os rom */
    uint8_t      bk_sel;
    uint16_t     bk_tab[16];
    uint16_t     bk_sys_d;
} sys;

static void fallback_log(enum retro_log_level level, const char *fmt, ...);
static retro_log_printf_t       log_cb = fallback_log;
static retro_environment_t      environ_cb;
static retro_video_refresh_t    video_cb;
static retro_input_poll_t       input_poll_cb;
static retro_input_state_t      input_state_cb;
static retro_audio_sample_t     audio_cb;
static uint16_t                 fb[(LCD_WIDTH + 1) * LCD_HEIGHT];


static void sys_isr();

static inline uint32_t PA(uint16_t addr)
{
    uint8_t bank = addr >> 12;
    return (sys.bk_tab[bank] << 12) | (addr & 0x0fff);
}

static uint8_t flash_read(uint32_t addr)
{
    static uint8_t flash_info[0x35] = {
        0xbf, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x51, 0x52, 0x59, 0x01, 0x07, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x27, 0x36, 0x00, 0x00, 0x04,
        0x00, 0x04, 0x06, 0x01, 0x00, 0x01, 0x01, 0x15,
        0x00, 0x00, 0x00, 0x00, 0x02, 0xff, 0x01, 0x10,
        0x00, 0x1f, 0x00, 0x00, 0x01,
    };
    if (sys.flash_cmd == 0 || sys.flash_cmd == 1)
        return sys.flash[addr];
    else
        // Software ID or CFI
        return flash_info[addr];
}

static void flash_write(uint32_t addr, uint8_t val)
{
    switch (sys.flash_cycles) {
    case 0:
        // 1st Bus Write Cycle
        if (addr == 0x5555 && val == 0xaa)
            sys.flash_cycles += 1;
        else if (val == 0xf0)
            // Software ID Exit / CFI Exit
            sys.flash_cmd = 0;
        break;
    case 1:
    case 4:
        // 2nd Bus Write Cycle / 5th Bus Write Cycle
        if (addr == 0x2aaa && val == 0x55)
            sys.flash_cycles += 1;
        break;
    case 2:
        // 3rd Bus Write Cycle
        if (addr != 0x5555)
            return;
        switch (val) {
        case 0xa0:
            // Byte-Program
            sys.flash_cmd = 1;
            sys.flash_cycles += 1;
            break;
        case 0x90:
            // Software ID Entry
            sys.flash_cmd = 2;
            sys.flash_cycles = 0;
            break;
        case 0x98:
            // CFI Query Entry
            sys.flash_cmd = 3;
            sys.flash_cycles = 0;
            break;
        case 0xf0:
            // Software ID Exit / CFI Exit
            sys.flash_cmd = 0;
            sys.flash_cycles = 0;
            break;
        }
        break;
    case 3:
        // 4th Bus Write Cycle
        if (sys.flash_cmd == 1) {
            sys.flash_cmd = 0;
            sys.flash_cycles = 0;
            sys.flash[addr] = val;
        } else if ((addr == 0x5555) && (val == 0xaa)) {
            sys.flash_cycles += 1;
        }
        break;
    case 5:
        // 6th Bus Write Cycle
        switch (val) {
        case 0x10:
            // Chip-Erase
            if (addr == 0x5555)
                memset(sys.flash, 0xff, 0x200000);
            break;
        case 0x30:
            // Sector-Erase
            memset(sys.flash + (addr & 0x1ff000), 0xff, 0x1000);
            break;
        case 0x50:
            // Block-Erase
            memset(sys.flash + (addr & 0x1f0000), 0xff, 0x10000);
            break;
        }
        sys.flash_cmd = 0;
        sys.flash_cycles = 0;
        break;
    }
}

static uint8_t mem_read(uint16_t addr, bool isDbg)
{
    uint32_t paddr = PA(addr);

    if ((addr < 0x20) || (addr >= 0x200 && addr < 0x2e0)) {
        switch (addr) {
        case _DATA1:
        case _DATA2:
        case _DATA3:
        case _DATA4: {
            int _L = _ADDR1L + addr * 3;
            int _M = _L + 1;
            int _H = _M + 1;
            paddr = sys.ram[_L] | sys.ram[_M] << 8 | sys.ram[_H] << 16;
            if (sys.ram[_INCR] & (1 << addr)) {
                sys.ram[_L] += 1;
                if (sys.ram[_L] == 0) {
                    sys.ram[_M] += 1;
                    if (sys.ram[_M] == 0) {
                        sys.ram[_H] += 1;
                    }
                }
            }
            break;
        }
        case _BK_SEL:
            return sys.bk_sel;
        case _BK_ADRL:
            return sys.bk_tab[sys.bk_sel] & 0xff;
        case _BK_ADRH:
            return sys.bk_tab[sys.bk_sel] >> 8;
        case _PB:
            // XXX: Disable ROM (0x400000-0x7fffff) channels and audio.
            return 0;
        case _MACCTL:
	    // XXX: Return BRK for game exit.
            return 0;
        }
    }

    // Never return 0 for AutoPowerOffCount to prevent poweroff.
    if (addr == 0x2028)
        return 0xff;

    if (addr >= 0x300 && addr < 0x400) {
        return sys.rom_e[0x1fff00 + addr - 0x300];
    } else if (paddr < 0x8000) {
        return sys.ram[paddr];
    } else if (paddr >= 0x200000 && paddr < 0x400000) {
        return flash_read(paddr - 0x200000);
    } else if (paddr >= 0x800000 && paddr < 0xa00000) {
        return sys.rom_8[paddr - 0x800000];
    } else if (paddr >= 0xe00000 && paddr < 0x1000000) {
        return sys.rom_e[paddr - 0xe00000];
    } else {
	// Invalid read.
        return 0x00;
    }
}

static uint16_t mem_read16(uint16_t addr)
{
    return mem_read(addr, false) | mem_read(addr + 1, false) << 8;
}

static void mem_write(uint16_t addr, uint8_t val)
{
    uint32_t paddr = PA(addr);

    if ((addr < 0x20) || (addr >= 0x200 && addr < 0x2e0)) {
        switch (addr) {
        case _DATA1:
        case _DATA2:
        case _DATA3:
        case _DATA4: {
            int _L = _ADDR1L + addr * 3;
            int _M = _L + 1;
            int _H = _M + 1;
            paddr = sys.ram[_L] | sys.ram[_M] << 8 | sys.ram[_H] << 16;
            if (sys.ram[_INCR] & (1 << addr)) {
                sys.ram[_L] += 1;
                if (sys.ram[_L] == 0) {
                    sys.ram[_M] += 1;
                    if (sys.ram[_M] == 0) {
                        sys.ram[_H] += 1;
                    }
                }
            }
            break;
        }
        case _ISR:
            sys.ram[_ISR] &= val;
            return;
        case _TISR:
            sys.ram[_TISR] &= val;
            return;
        case _BK_SEL:
            sys.bk_sel = val & 0x0f;
            return;
        case _BK_ADRL:
            sys.bk_tab[sys.bk_sel] &= 0xff00;
            sys.bk_tab[sys.bk_sel] |= val;
            return;
        case _BK_ADRH:
            sys.bk_tab[sys.bk_sel] &= 0x00ff;
            sys.bk_tab[sys.bk_sel] |= (val & 0x0f) << 8;
            return;
        }
    }

    if (paddr < 0x8000) {
        sys.ram[paddr] = val;
    } else if (paddr >= 0x200000 && paddr < 0x400000) {
        flash_write(paddr - 0x200000, val);
    } else {
	// Invalid write.
    }
}

enum _key {
    KEY_0 = 0x31,
    KEY_1 = 0x08,
    KEY_2 = 0x09,
    KEY_3 = 0x0a,
    KEY_4 = 0x0b,
    KEY_5 = 0x0c,
    KEY_6 = 0x0d,
    KEY_7 = 0x0e,
    KEY_8 = 0x0f,
    KEY_9 = 0x30,
    KEY_SPACE = 0x36,
    KEY_EXIT = 0x2e,
    KEY_ENTER = 0x2f,
    KEY_UP = 0x35,
    KEY_DOWN = 0x38,
    KEY_LEFT = 0x37,
    KEY_RIGHT = 0x39,
    KEY_PGUP = 0x3a,
    KEY_PGDN = 0x3b,
};

static uint8_t _joyk[16] = {
    [RETRO_DEVICE_ID_JOYPAD_B] = KEY_EXIT,
    [RETRO_DEVICE_ID_JOYPAD_Y] = KEY_SPACE,
    [RETRO_DEVICE_ID_JOYPAD_SELECT] = KEY_EXIT,
    [RETRO_DEVICE_ID_JOYPAD_START] = KEY_ENTER,
    [RETRO_DEVICE_ID_JOYPAD_UP] = KEY_UP,
    [RETRO_DEVICE_ID_JOYPAD_DOWN] = KEY_DOWN,
    [RETRO_DEVICE_ID_JOYPAD_LEFT] = KEY_LEFT,
    [RETRO_DEVICE_ID_JOYPAD_RIGHT] = KEY_RIGHT,
    [RETRO_DEVICE_ID_JOYPAD_A] = KEY_ENTER,
    [RETRO_DEVICE_ID_JOYPAD_X] = KEY_ENTER,
    [RETRO_DEVICE_ID_JOYPAD_L] = KEY_PGUP,
    [RETRO_DEVICE_ID_JOYPAD_R] = KEY_PGDN,
    [RETRO_DEVICE_ID_JOYPAD_L2] = KEY_PGUP,
    [RETRO_DEVICE_ID_JOYPAD_R2] = KEY_PGDN,
    [RETRO_DEVICE_ID_JOYPAD_L3] = KEY_PGUP,
    [RETRO_DEVICE_ID_JOYPAD_R3] = KEY_PGDN,
};

static uint8_t _kbdk[RETROK_LAST] = {
    [RETROK_0] = KEY_0,
    [RETROK_1] = KEY_1,
    [RETROK_2] = KEY_2,
    [RETROK_3] = KEY_3,
    [RETROK_4] = KEY_4,
    [RETROK_5] = KEY_5,
    [RETROK_6] = KEY_6,
    [RETROK_7] = KEY_7,
    [RETROK_8] = KEY_8,
    [RETROK_9] = KEY_9,
    [RETROK_SPACE] = KEY_SPACE,
    [RETROK_ESCAPE] = KEY_EXIT,
    [RETROK_RETURN] = KEY_ENTER,
    [RETROK_UP] = KEY_UP,
    [RETROK_DOWN] = KEY_DOWN,
    [RETROK_LEFT] = KEY_LEFT,
    [RETROK_RIGHT] = KEY_RIGHT,
    [RETROK_PAGEUP] = KEY_PGUP,
    [RETROK_PAGEDOWN] = KEY_PGDN,
};

static void sys_keydown(uint8_t key)
{
    if (key == 0)
        return;
    sys.ram[_SYSCON] &= 0xf7;
    sys.ram[_KEYCODE] = key | 0x80;
    sys.ram[_ISR] |= 0x80;
    sys_isr();
}

static void keyboard_cb(bool down, unsigned keycode,
                        uint32_t character, uint16_t key_modifiers)
{
    if (!down)
        return;
    sys_keydown(_kbdk[keycode]);
}

static void sys_init()
{
    FILE *stream;
    stream = fopen("2.BIN", "r");
    fread(sys.flash, 0x200000, 1, stream);
    fclose(stream);
    stream = fopen("8.BIN", "r");
    fread(sys.rom_8, 0x200000, 1, stream);
    fclose(stream);
    stream = fopen("E.BIN", "r");
    fread(sys.rom_e, 0x200000, 1, stream);
    fclose(stream);

    memset(sys.ram, 0x00, 0x8000);
    sys.flash_cmd = 0;
    sys.flash_cycles = 0;
    sys.ram[_INCR] = 0x0f;

    sys.cpu = vrEmu6502New(CPU_6502, mem_read, mem_write);
    vrEmu6502SetPC(sys.cpu, 0x0350);

    // Run initialize instructions until 'main'.
    while (!(sys.cpu->pc == 0xd2f6 &&
             sys.ram[__addr_reg] == 0x37 && sys.ram[__addr_reg+1] == 0xe7))
        vrEmu6502InstCycle(sys.cpu);
    sys.bk_sys_d = sys.bk_tab[0xd];
}

static void sys_deinit()
{
    vrEmu6502Destroy(sys.cpu);
}

static void sys_load(const uint8_t *gam, size_t size)
{
    uint16_t start = gam[0x40] | (gam[0x41] << 8);
    uint32_t data = gam[0x42] | gam[0x43] << 8 | gam[0x44] << 16 | gam[0x45] << 24;

    // Load game into 0x205000.
    // TODO: Handle file headers and saves.
    memset(sys.flash, 0xff, 0x200000);
    memcpy(sys.flash+0x5000, gam, size);
    // Setup banks for the game.
    sys.bk_tab[0x5] = 0x205;
    sys.bk_tab[0x6] = 0x206;
    sys.bk_tab[0x7] = 0x207;
    sys.bk_tab[0x8] = 0x208;
    sys.bk_tab[0x9] = 0x205 + (data >> 12);
    sys.bk_tab[0xa] = sys.bk_tab[0x09] + 1;
    sys.bk_tab[0xb] = sys.bk_tab[0x09] + 2;
    sys.bk_tab[0xc] = sys.bk_tab[0x09] + 3;
    mem_write(0x2029, 0x05);
    mem_write(0x202a, 0x02);
    // Push game return address, 0x0260=BRK.
    push(sys.cpu, 0x02);
    push(sys.cpu, 0x60);
    // Start the game.
    vrEmu6502SetPC(sys.cpu, start);
}

static void sys_timer(uint32_t n)
{
    static uint32_t t[5] = { 0 };

    for (int i = 0; i < 4; i += 1) {
        if (sys.ram[_STCON] & (1 << i)) {
            t[i] += n;
            if (t[i] >= 0x100) {
                t[i] = sys.ram[_ST1LD + i];
                if (sys.ram[_TIER] & (1 << i)) {
                    sys.ram[_TISR] |= (1 << i);
                    sys.ram[_SYSCON] &= 0xf7;
                }
            }
        }
    }

    if (sys.ram[_STCTCON] & 0x10) {
        t[4] += n;
        if (t[4] >= 0x1000) {
            t[4] = sys.ram[_CTLD];
            if (sys.ram[_IER] & 0x02) {
                sys.ram[_ISR] |= 0x02;
                sys.ram[_SYSCON] &= 0xf7;
            }
        }
    }
 }

static void sys_rtc()
{
    if ((sys.ram[_STCTCON] & 0x40) == 0x00)
        return;

    if (sys.ram[_RTCSEC]++ == 59) {
        sys.ram[_RTCSEC] = 0;
        if (sys.ram[_RTCMIN]++ == 59) {
            sys.ram[_RTCMIN] = 0;
            if (sys.ram[_RTCHR]++ == 23) {
                sys.ram[_RTCHR] = 0;
                if (sys.ram[_RTCDAYL]++ == 0xff) {
                    if (sys.ram[_RTCDAYH]++ == 1) {
                        sys.ram[_RTCDAYH] = 0;
                    }
                }
            }
        }
    }
    if ((sys.ram[_STCTCON] & 0x20) == 0x00)
        return;
    if ((sys.ram[_RTCMIN] == sys.ram[_ALMMIN]) &&
        (sys.ram[_RTCHR] == sys.ram[_ALMHR]) &&
        (sys.ram[_RTCDAYL] == sys.ram[_ALMDAYL]) &&
        (sys.ram[_RTCDAYH] == sys.ram[_ALMDAYH])) {
        sys.ram[_ISR] |= 0x01;
    }
}


static void sys_isr()
{
    uint8_t idx = 0;
    if (sys.cpu->flags & FlagI)
        return;
    if ((sys.ram[_ISR] & 0x80) && (sys.ram[_IER] & 0x80)) {
        idx = 0x02; // PI
	sys.ram[_ISR] &= 0x7f;
	return;
    } else if ((sys.ram[_ISR] & 0x01) && (sys.ram[_IER] & 0x01)) {
        idx = 0x13; // ALM
    } else if ((sys.ram[_ISR] & 0x02) && (sys.ram[_IER] & 0x02)) {
        idx = 0x12; // CT
    } else if ((sys.ram[_TISR] & 0x20) && (sys.ram[_TIER] & 0x20)) {
        idx = 0x11; // MT
    } else if ((sys.ram[_TISR] & 0x80) && (sys.ram[_TIER] & 0x80)) {
        idx = 0x10; // GTH
    } else if ((sys.ram[_TISR] & 0x40) && (sys.ram[_TIER] & 0x40)) {
        idx = 0x0f; // GTL
    }  else if ((sys.ram[_TISR] & 0x01) && (sys.ram[_TIER] & 0x01)) {
        idx = 0x03; // ST1
	sys.ram[_TISR] &= 0xfe;
	sys.ram[0x2018] += 1;
	if (sys.ram[0x2018] >= sys.ram[0x2019]) {
	    sys.ram[0x201e] |= 0x01;
	    sys.ram[0x2018] = 0;
	}
	return;
    } else if ((sys.ram[_TISR] & 0x02) && (sys.ram[_TIER] & 0x02)) {
        idx = 0x04; // ST2
    } else if ((sys.ram[_TISR] & 0x04) && (sys.ram[_TIER] & 0x04)) {
        idx = 0x05; // ST3
    } else if ((sys.ram[_TISR] & 0x08) && (sys.ram[_TIER] & 0x08)) {
        idx = 0x06; // ST4
    } else {
        return;
    }

    push(sys.cpu, sys.cpu->pc >> 8);
    push(sys.cpu, sys.cpu->pc & 0xff);
    push(sys.cpu, sys.cpu->flags);
    setBit(sys.cpu, FlagI);
    vrEmu6502SetPC(sys.cpu, 0x0300 + idx * 4);
}

static void sys_step()
{
    uint32_t cycles = 0;

    while ((sys.ram[_SYSCON] & 0x80) == 0 && cycles < 300000) {
        if (sys.bk_tab[0xd] == sys.bk_sys_d &&
            vrEmu6502GetNextOpcode(sys.cpu) == 0x20) { // JSR $xxxx
            // High level emulation for system functions.
            uint16_t func = mem_read16(sys.cpu->pc + 1);
            if (func == 0xd2f6) { // __banked_function_call
                func = mem_read16(__addr_reg);
                if (func == 0xe7a0) {
                    // SysHalt
                    if ((sys.ram[0x2021] & 0x02) == 0) {
                        sys.ram[_SYSCON] |= 0x08;
                    }
                    sys.cpu->pc += 3;
                    break;
                }
                if (func == 0xe7c1) {
                    // SysGetKey
                    if (sys.ram[_KEYCODE] & 0x80) {
                        sys.cpu->ac = sys.ram[_KEYCODE] & 0x3f;
                        sys.ram[_KEYCODE] = 0;
                    } else {
                        sys.cpu->ac = 0xff;
                    }
                    sys.cpu->pc += 3;
                    continue;
                }
            }
        }

	if (vrEmu6502GetNextOpcode(sys.cpu) == 0) {
	    // Upon BRK, shutdown the game.
	    sys.ram[_SYSCON] |= 0x08;
	    environ_cb(RETRO_ENVIRONMENT_SHUTDOWN, NULL);
	    break;
	}
	cycles += vrEmu6502InstCycle(sys.cpu);
    }
}

static void fallback_log(enum retro_log_level level, const char *fmt, ...)
{
    (void)level;
    va_list va;
    va_start(va, fmt);
    vfprintf(stderr, fmt, va);
    va_end(va);
}

unsigned retro_api_version(void)
{
    return RETRO_API_VERSION;
}

static void frame_cb(retro_usec_t usec)
{
    static uint32_t ms = 0;
    ms += usec / 1000;
    if (ms > 1000) {
        ms -= 1000;
        sys_rtc();
    }
    sys_timer(usec / 100);
    sys_isr();
}

void retro_set_environment(retro_environment_t cb)
{
    static bool yes = true;
    static struct retro_log_callback log;
    static struct retro_keyboard_callback kbd = {
        .callback = keyboard_cb,
    };
    static struct retro_frame_time_callback frame = {
        .callback = frame_cb,
        .reference = 1000000 / 60,
    };
    environ_cb = cb;
    if (environ_cb(RETRO_ENVIRONMENT_GET_LOG_INTERFACE, &log))
        log_cb = log.log;
    environ_cb(RETRO_ENVIRONMENT_SET_SUPPORT_NO_GAME, &yes);
    environ_cb(RETRO_ENVIRONMENT_SET_FRAME_TIME_CALLBACK, &frame);
    environ_cb(RETRO_ENVIRONMENT_SET_KEYBOARD_CALLBACK, &kbd);
}

void retro_set_video_refresh(retro_video_refresh_t cb)
{
    video_cb = cb;
}

void retro_set_audio_sample(retro_audio_sample_t cb)
{
    audio_cb = cb;
}

void retro_set_audio_sample_batch(retro_audio_sample_batch_t cb)
{
}

void retro_set_input_poll(retro_input_poll_t cb)
{
    input_poll_cb = cb;
}

void retro_set_input_state(retro_input_state_t cb)
{
    input_state_cb = cb;
}

void retro_get_system_info(struct retro_system_info *info)
{
    info->need_fullpath = false;
    info->valid_extensions = "gam";
    info->library_version = "0.1";
    info->library_name = "gam4980";
    info->block_extract = false;
}

void retro_get_system_av_info(struct retro_system_av_info *info)
{
    info->geometry.base_width = LCD_WIDTH;
    info->geometry.base_height = LCD_HEIGHT;
    info->geometry.max_width = LCD_WIDTH;
    info->geometry.max_height = LCD_HEIGHT;
    info->geometry.aspect_ratio = 0.0;
    info->timing.fps = 60.0;
    info->timing.sample_rate = 44100;

    static enum retro_pixel_format pixfmt = RETRO_PIXEL_FORMAT_RGB565;
    environ_cb(RETRO_ENVIRONMENT_SET_PIXEL_FORMAT, &pixfmt);
}

void retro_init(void)
{
    sys_init();
}

bool retro_load_game(const struct retro_game_info *game)
{
    if (game == NULL)
        return true;
    if (game->data == NULL)
        return false;
    sys_load(game->data, game->size);
    return true;
}

void retro_set_controller_port_device(unsigned port, unsigned device)
{
}

void retro_deinit(void)
{
    sys_deinit();
}

void retro_reset(void)
{
}

static inline void pp8(int y, int x, uint8_t p8)
{
    // Draw 8 pixels.
    for (int i = 0; i < 8; i += 1) {
        bool p = p8 & (1 << (7 - i));
        fb[y * LCD_WIDTH + x * 8 + i] = p ? 0x0000 : 0xffff;
    }
}

void retro_run(void)
{
    input_poll_cb();

    // Only accept new joypad press when the last one is released.
    static int pressed = -1;
    for (int i = 0; i < 16; i += 1) {
        if (pressed == i) {
            if (input_state_cb(0, RETRO_DEVICE_JOYPAD, 0, i) == 0)
                pressed = -1;
        }
        if (pressed == -1 && input_state_cb(0, RETRO_DEVICE_JOYPAD, 0, i)) {
            pressed = i;
            sys_keydown(_joyk[i]);
            break;
        }
    }

    sys_step();

    // Draw the screen.
    uint8_t *v = sys.ram + 0x400;
    for (int j = 65; j >= -30; j -= 1) {
        for (int i = 1; i < 20; i += 1) {
            pp8(j >= 0 ? j : (j * -1 + 65), i, *v++);
        }
        v += 13;
    }
    v = sys.ram + 0x413;
    for (int j = 64; j >= -30; j -= 1) {
        pp8(j >= 0 ? j : (j * -1 + 65), 0, *v++);
        v += 31;
    }
    pp8(65, 0, sys.ram[0x0ff3]);
    pp8(65, 1, sys.ram[0x1000]);
    video_cb(fb, LCD_WIDTH, LCD_HEIGHT, 2 * LCD_WIDTH);
}

size_t retro_serialize_size(void)
{
    return 0;
}

bool retro_serialize(void *data, size_t size)
{
    return false;
}

bool retro_unserialize(const void *data, size_t size)
{
    return false;
}

void retro_cheat_reset(void) {}
void retro_cheat_set(unsigned index, bool enabled, const char *code) {}

bool retro_load_game_special(unsigned game_type, const struct retro_game_info *info, size_t num_info)
{
    return false;
}

void retro_unload_game(void)
{
}

unsigned retro_get_region(void)
{
    return RETRO_REGION_NTSC;
}

void *retro_get_memory_data(unsigned id)
{
    return NULL;
}

size_t retro_get_memory_size(unsigned id)
{
    return 0;
}
