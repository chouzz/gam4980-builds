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
#define __oper1         0x20
#define __oper2         0x23
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
    uint8_t     *mem_r[0x100];
    uint8_t    (*mem_ir[0x100])(uint16_t);
    void       (*mem_iw[0x100])(uint16_t, uint8_t);
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
static struct {
    uint8_t cpu_rate;
    uint8_t timer_rate;
    uint16_t lcd_bg;
    uint16_t lcd_fg;
} vars = { 1, 1, 0xd6da, 0x0000 };

static void fallback_log(enum retro_log_level level, const char *fmt, ...);
static retro_log_printf_t       log_cb = fallback_log;
static retro_environment_t      environ_cb;
static retro_video_refresh_t    video_cb;
static retro_input_poll_t       input_poll_cb;
static retro_input_state_t      input_state_cb;
static retro_audio_sample_t     audio_cb;
static uint16_t                 fb[(LCD_WIDTH + 1) * LCD_HEIGHT];

static void sys_isr();
static void mem_bs(uint8_t sel);

static inline uint32_t PA(uint16_t addr)
{
    uint8_t bank = addr >> 12;
    return (sys.bk_tab[bank] << 12) | (addr & 0x0fff);
}

static uint8_t flash_read(uint32_t addr)
{
    static uint8_t flash_info[0x35] = {
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x51, 0x52, 0x59, 0x01, 0x07, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x27, 0x36, 0x00, 0x00, 0x04,
        0x00, 0x04, 0x06, 0x01, 0x00, 0x01, 0x01, 0x15,
        0x00, 0x00, 0x00, 0x00, 0x02, 0xff, 0x01, 0x10,
        0x00, 0x1f, 0x00, 0x00, 0x01,
    };
    if (sys.flash_cmd == 0 || sys.flash_cmd == 1) {
        // Rotate last 32KiB to the front for save.
        addr = (addr + 0x8000) % 0x200000;
        return sys.flash[addr];
    } else {
        // Software ID or CFI
        return flash_info[addr];
    }
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
        case 0x80:
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
            // Rotate last 32KiB to the front for save.
            addr = (addr + 0x8000) % 0x200000;
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
            addr = (addr + 0x8000) % 0x200000;
            memset(sys.flash + (addr & 0x1ff000), 0xff, 0x1000);
            break;
        case 0x50:
            // Block-Erase
            addr = ((addr & 0x1f0000) + 0x8000) % 0x200000;
            memset(sys.flash + addr, 0xff, 0x8000);
            addr = (addr + 0x8000) % 0x200000;
            memset(sys.flash + addr, 0xff, 0x8000);
            break;
        }
        sys.flash_cmd = 0;
        sys.flash_cycles = 0;
        break;
    }

    // Read CFI/ID info via 'sys.mem_ir'.
    if (sys.flash_cmd == 2 || sys.flash_cmd == 3) {
        for (int i = 0; i < 0x100; i += 1) {
            if (sys.mem_r[i] >= sys.flash && sys.mem_r[i] < sys.flash + 0x200000) {
                sys.mem_r[i] = 0;
            }
        }
    }
}

static uint8_t invalid_read(uint16_t addr)
{
    return 0x00;
}

static void invalid_write(uint16_t addr, uint8_t val)
{
}

static uint8_t ram_read(uint16_t addr)
{
    return sys.ram[addr];
}

static void ram_write(uint16_t addr, uint8_t val)
{
    sys.ram[addr] = val;

    // XXX: Disable ROM (0x400000-0x7fffff) channels and audio.
    if (addr == _PB)
        sys.ram[addr] = 0;

    // Never return 0 for AutoPowerOffCount to prevent poweroff.
    if (addr == 0x2028)
        sys.ram[addr] = 0xff;
}

static uint8_t direct_read(uint16_t addr)
{
    int _L = _ADDR1L + addr * 3;
    int _M = _L + 1;
    int _H = _M + 1;
    uint32_t paddr = sys.ram[_L] | sys.ram[_M] << 8 | sys.ram[_H] << 16;
    if (sys.ram[_INCR] & (1 << addr)) {
        sys.ram[_L] += 1;
        if (sys.ram[_L] == 0) {
            sys.ram[_M] += 1;
            if (sys.ram[_M] == 0) {
                sys.ram[_H] += 1;
            }
        }
    }
    if (paddr < 0x8000)
        return ram_read(paddr & 0x7fff);
    else if (paddr >= 0x200000 && paddr < 0x400000)
        return flash_read(paddr - 0x200000);
    else if (paddr >= 0x800000 && paddr < 0xa00000)
        return sys.rom_8[paddr - 0x800000];
    else if (paddr >= 0xe00000 && paddr < 0x1000000)
        return sys.rom_e[paddr - 0xe00000];
    else
        return 0x00;
}

static void direct_write(uint16_t addr, uint8_t val)
{
    int _L = _ADDR1L + addr * 3;
    int _M = _L + 1;
    int _H = _M + 1;
    uint32_t paddr = sys.ram[_L] | sys.ram[_M] << 8 | sys.ram[_H] << 16;
    if (sys.ram[_INCR] & (1 << addr)) {
        sys.ram[_L] += 1;
        if (sys.ram[_L] == 0) {
            sys.ram[_M] += 1;
            if (sys.ram[_M] == 0) {
                sys.ram[_H] += 1;
            }
        }
    }
    if (paddr < 0x8000)
        ram_write(paddr & 0x7fff, val);
    else if (paddr >= 0x200000 && paddr < 0x400000)
        flash_write(paddr - 0x200000, val);
}

static uint8_t page0_read(uint16_t addr)
{
    switch (addr) {
    case _DATA1:
    case _DATA2:
    case _DATA3:
    case _DATA4:
        return direct_read(addr);
    case _BK_SEL:
        return sys.bk_sel;
    case _BK_ADRL:
        return sys.bk_tab[sys.bk_sel] & 0xff;
    case _BK_ADRH:
        return sys.bk_tab[sys.bk_sel] >> 8;
    }
    return sys.ram[addr];
}

static void page0_write(uint16_t addr, uint8_t val)
{
    switch (addr) {
    case _DATA1:
    case _DATA2:
    case _DATA3:
    case _DATA4:
        direct_write(addr, val);
        return;
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
        mem_bs(sys.bk_sel);
        return;
    case _BK_ADRH:
        sys.bk_tab[sys.bk_sel] &= 0x00ff;
        sys.bk_tab[sys.bk_sel] |= (val & 0x0f) << 8;
        mem_bs(sys.bk_sel);
        return;
    }
    sys.ram[addr] = val;
}

static void mem_init()
{
    for (int i = 0; i < 0x100; i += 1) {
        sys.mem_r[i] = 0;
        sys.mem_ir[i] = invalid_read;
        sys.mem_iw[i] = invalid_write;
    }
    for (int i = 1; i < 16; i += 1) {
        sys.mem_r[i] = sys.ram + i * 0x100;
        sys.mem_ir[i] = ram_read;
        sys.mem_iw[i] = ram_write;
    }
    sys.mem_ir[0x00] = page0_read;
    sys.mem_iw[0x00] = page0_write;
    sys.mem_r[0x03] = sys.rom_e + 0x1fff00;
    sys.mem_iw[0x03] = invalid_write;
}

static uint8_t flash_vread(uint16_t addr)
{
    return flash_read(PA(addr) - 0x200000);
}

static void flash_vwrite(uint16_t addr, uint8_t val)
{
    return flash_write(PA(addr) - 0x200000, val);
}

static uint8_t rom_8_vread(uint16_t addr)
{
    return sys.rom_8[PA(addr) - 0x800000];
}

static uint8_t rom_e_vread(uint16_t addr)
{
    return sys.rom_e[PA(addr) - 0xe00000];
}

static uint8_t ram_vread(uint16_t addr)
{
    return ram_read(PA(addr));
}

static void ram_vwrite(uint16_t addr, uint8_t val)
{
    ram_write(PA(addr), val);
}

static void mem_bs(uint8_t sel)
{
    uint32_t paddr = PA(sel * 0x1000);
    if (sel == 0)
        return;
    if (paddr < 0x8000) {
        for (int i = 0; i < 16; i += 1) {
            sys.mem_r[sel * 16 + i] = sys.ram + paddr + i * 0x100;
            sys.mem_ir[sel * 16 + i] = ram_vread;
            sys.mem_iw[sel * 16 + i] = ram_vwrite;
        }
    } else if (paddr >= 0x200000 && paddr < 0x400000) {
        for (int i = 0; i < 16; i += 1) {
            uint32_t faddr = (paddr - 0x200000 + 0x8000) % 0x200000;
            sys.mem_r[sel * 16 + i] = sys.flash + faddr + i * 0x100;
            sys.mem_ir[sel * 16 + i] = flash_vread;
            sys.mem_iw[sel * 16 + i] = flash_vwrite;
        }
    } else if (paddr >= 0x800000 && paddr < 0xa00000) {
        for (int i = 0; i < 16; i += 1) {
            sys.mem_r[sel * 16 + i] = sys.rom_8 + paddr - 0x800000 + i * 0x100;
            sys.mem_ir[sel * 16 + i] = rom_8_vread;
            sys.mem_iw[sel * 16 + i] = invalid_write;
        }
    } else if (paddr >= 0xe00000 && paddr < 0x1000000) {
        for (int i = 0; i < 16; i += 1) {
            sys.mem_r[sel * 16 + i] = sys.rom_e + paddr - 0xe00000 + i * 0x100;
            sys.mem_ir[sel * 16 + i] = rom_e_vread;
            sys.mem_iw[sel * 16 + i] = invalid_write;
        }
    } else {
        for (int i = 0; i < 16; i += 1) {
            sys.mem_r[sel * 16 + i] = 0;
            sys.mem_ir[sel * 16 + i] = invalid_read;
            sys.mem_iw[sel * 16 + i] = invalid_write;
        }
    }
}

static uint8_t mem_read(uint16_t addr, bool isDbg)
{
    uint8_t page = addr >> 8;
    if (sys.mem_r[page])
        return sys.mem_r[page][addr & 0xff];
    else
        return sys.mem_ir[page](addr);
}

static uint16_t mem_read16(uint16_t addr)
{
    return mem_read(addr, false) | mem_read(addr + 1, false) << 8;
}

static void mem_write(uint16_t addr, uint8_t val)
{
    return sys.mem_iw[addr >> 8](addr, val);
}

enum _key {
    KEY_ON_OFF    = 0x00,       /* 开关 */
    KEY_HOME_MENU = 0x01,       /* 目录 */
    KEY_EC_SJ     = 0x02,       /* 双解 */
    KEY_EC_SW     = 0x03,       /* 十万 */
    KEY_CE        = 0x04,       /* 汉英 */
    KEY_DLG       = 0x05,       /* 对话 */
    KEY_DOWNLOAD  = 0x06,       /* 下载 */
    KEY_SPK       = 0x07,       /* 发音 */
    KEY_1         = 0x08,
    KEY_2         = 0x09,
    KEY_3         = 0x0a,
    KEY_4         = 0x0b,
    KEY_5         = 0x0c,
    KEY_6         = 0x0d,
    KEY_7         = 0x0e,
    KEY_8         = 0x0f,
    KEY_9         = 0x30,
    KEY_0         = 0x31,
    KEY_Q         = 0x10,
    KEY_W         = 0x11,
    KEY_E         = 0x12,
    KEY_R         = 0x13,
    KEY_T         = 0x14,
    KEY_Y         = 0x15,
    KEY_U         = 0x16,
    KEY_I         = 0x17,
    KEY_O         = 0x32,
    KEY_P         = 0x33,
    KEY_SPACE     = 0x36,       /* 空格 */
    KEY_A         = 0x18,
    KEY_S         = 0x19,
    KEY_D         = 0x1a,
    KEY_F         = 0x1b,
    KEY_G         = 0x1c,
    KEY_H         = 0x1d,
    KEY_J         = 0x1e,
    KEY_K         = 0x1f,
    KEY_L         = 0x34,
    KEY_INPUT     = 0x20,       /* 输入法 */
    KEY_CAPS      = KEY_INPUT,
    KEY_Z         = 0x21,
    KEY_X         = 0x22,
    KEY_C         = 0x23,
    KEY_V         = 0x24,
    KEY_B         = 0x25,
    KEY_N         = 0x26,
    KEY_M         = 0x27,
    KEY_ZY        = 0x28,       /* 中英 */
    KEY_SHIFT     = KEY_ZY,
    KEY_HELP      = 0x29,       /* 帮助 */
    KEY_SEARCH    = 0x2a,       /* 查找 */
    KEY_INSERT    = 0x2b,       /* 插入 */
    KEY_MODIFY    = 0x2c,       /* 修改 */
    KEY_DEL       = 0x2d,       /* 删除 */
    KEY_EXIT      = 0x2e,       /* 跳出 */
    KEY_ENTER     = 0x2f,       /* 输入 */
    KEY_UP        = 0x35,
    KEY_DOWN      = 0x38,
    KEY_LEFT      = 0x37,
    KEY_RIGHT     = 0x39,
    KEY_PGUP      = 0x3a,
    KEY_PGDN      = 0x3b,
};

static uint8_t _joyk[16] = {
    [RETRO_DEVICE_ID_JOYPAD_B]      = KEY_EXIT,
    [RETRO_DEVICE_ID_JOYPAD_Y]      = KEY_HELP,
    [RETRO_DEVICE_ID_JOYPAD_SELECT] = KEY_INSERT,
    [RETRO_DEVICE_ID_JOYPAD_START]  = KEY_SEARCH,
    [RETRO_DEVICE_ID_JOYPAD_UP]     = KEY_UP,
    [RETRO_DEVICE_ID_JOYPAD_DOWN]   = KEY_DOWN,
    [RETRO_DEVICE_ID_JOYPAD_LEFT]   = KEY_LEFT,
    [RETRO_DEVICE_ID_JOYPAD_RIGHT]  = KEY_RIGHT,
    [RETRO_DEVICE_ID_JOYPAD_A]      = KEY_ENTER,
    [RETRO_DEVICE_ID_JOYPAD_X]      = KEY_R,
    [RETRO_DEVICE_ID_JOYPAD_L]      = KEY_PGUP,
    [RETRO_DEVICE_ID_JOYPAD_R]      = KEY_PGDN,
    [RETRO_DEVICE_ID_JOYPAD_L2]     = KEY_MODIFY,
    [RETRO_DEVICE_ID_JOYPAD_R2]     = KEY_DEL,
    [RETRO_DEVICE_ID_JOYPAD_L3]     = KEY_A,
    [RETRO_DEVICE_ID_JOYPAD_R3]     = KEY_Z,
};

static uint8_t _kbdk[RETROK_LAST] = {
    [RETROK_F1]        = KEY_ON_OFF,
    [RETROK_F2]        = KEY_HOME_MENU,
    [RETROK_F3]        = KEY_EC_SJ,
    [RETROK_F4]        = KEY_EC_SW,
    [RETROK_F5]        = KEY_CE,
    [RETROK_F6]        = KEY_DLG,
    [RETROK_F7]        = KEY_DOWNLOAD,
    [RETROK_F8]        = KEY_SPK,
    [RETROK_F9]        = KEY_HELP,
    [RETROK_F10]       = KEY_SEARCH,
    [RETROK_F11]       = KEY_INSERT,
    [RETROK_F12]       = KEY_MODIFY,
    [RETROK_1]         = KEY_1,
    [RETROK_2]         = KEY_2,
    [RETROK_3]         = KEY_3,
    [RETROK_4]         = KEY_4,
    [RETROK_5]         = KEY_5,
    [RETROK_6]         = KEY_6,
    [RETROK_7]         = KEY_7,
    [RETROK_8]         = KEY_8,
    [RETROK_9]         = KEY_9,
    [RETROK_0]         = KEY_0,
    [RETROK_q]         = KEY_Q,
    [RETROK_w]         = KEY_W,
    [RETROK_e]         = KEY_E,
    [RETROK_r]         = KEY_R,
    [RETROK_t]         = KEY_T,
    [RETROK_y]         = KEY_Y,
    [RETROK_u]         = KEY_U,
    [RETROK_i]         = KEY_I,
    [RETROK_o]         = KEY_O,
    [RETROK_p]         = KEY_P,
    [RETROK_SPACE]     = KEY_SPACE,
    [RETROK_a]         = KEY_A,
    [RETROK_s]         = KEY_S,
    [RETROK_d]         = KEY_D,
    [RETROK_f]         = KEY_F,
    [RETROK_g]         = KEY_G,
    [RETROK_h]         = KEY_H,
    [RETROK_j]         = KEY_J,
    [RETROK_k]         = KEY_K,
    [RETROK_l]         = KEY_L,
    [RETROK_CAPSLOCK]  = KEY_INPUT,
    [RETROK_z]         = KEY_Z,
    [RETROK_x]         = KEY_X,
    [RETROK_c]         = KEY_C,
    [RETROK_v]         = KEY_V,
    [RETROK_b]         = KEY_B,
    [RETROK_n]         = KEY_N,
    [RETROK_m]         = KEY_M,
    [RETROK_LSHIFT]    = KEY_SHIFT,
    [RETROK_BACKSPACE] = KEY_DEL,
    [RETROK_DELETE]    = KEY_DEL,
    [RETROK_ESCAPE]    = KEY_EXIT,
    [RETROK_RETURN]    = KEY_ENTER,
    [RETROK_UP]        = KEY_UP,
    [RETROK_DOWN]      = KEY_DOWN,
    [RETROK_LEFT]      = KEY_LEFT,
    [RETROK_RIGHT]     = KEY_RIGHT,
    [RETROK_PAGEUP]    = KEY_PGUP,
    [RETROK_PAGEDOWN]  = KEY_PGDN,
};

static void sys_keydown(uint8_t key)
{
    if (key == 0)
        return;
    sys.ram[_SYSCON] &= 0xf7;
    sys.ram[_KEYCODE] = key | 0x80;
    sys.ram[_ISR] |= 0x80;
}

static void keyboard_cb(bool down, unsigned keycode,
                        uint32_t character, uint16_t key_modifiers)
{
    if (!down)
        return;
    sys_keydown(_kbdk[keycode]);
}

static void sys_init(const char *romdir)
{
    char path[512];
    FILE *stream;
    snprintf(path, 512, "%s/8.BIN", romdir);
    stream = fopen(path, "r");
    fread(sys.rom_8, 0x200000, 1, stream);
    fclose(stream);
    snprintf(path, 512, "%s/E.BIN", romdir);
    stream = fopen(path, "r");
    fread(sys.rom_e, 0x200000, 1, stream);
    fclose(stream);

    memset(sys.ram, 0x00, 0x8000);
    memset(sys.flash, 0xff, 0x200000);
    sys.flash_cmd = 0;
    sys.flash_cycles = 0;
    sys.ram[_INCR] = 0x0f;

    mem_init();
    sys.cpu = vrEmu6502New(CPU_W65C02, mem_read, mem_write);
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
    uint8_t sys_hdr[16] = {
        0xc0, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x10, 0x00, 0x2f,
    };
    uint8_t gam_hdr[16] = {
        0xd0, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00,
        size & 0xff, (size >> 8) & 0xff, (size >> 16) * 0xff,
        0x3d,
    };

    // Setup file headers.
    uint8_t *flash = sys.flash + 0x8000;
    memcpy(gam_hdr + 2, gam + 6, 0x0a);
    memcpy(flash, sys_hdr, 16);
    memcpy(flash+16, gam_hdr, 16);
    // Load game into 0x20d000.
    memcpy(flash+0xd000, gam, size);
    memset(flash+0x1000, 0x01, 0x100);
    for (int i = 0; i < 0x0c; i += 1) {
        flash[0x1000 + i] = 0x04;
    }

    if (sys.bk_sys_d == 0x0ea8) { /* A4980 */
        memset(flash+0x7000, 0x01, 0x100);
        // Last 32 KiB for save file.
        flash[0x70f8] = 0x02;
        flash[0x70f9] = 0x02;
        flash[0x70fa] = 0x02;
        flash[0x70fb] = 0x02;
        flash[0x70fc] = 0x02;
        flash[0x70fd] = 0x02;
        flash[0x70fe] = 0x03;
        flash[0x70ff] = 0x02;
    } else if (sys.bk_sys_d == 0x0e88) { /* A4988 */
        memset(flash+0x8000, 0x01, 0x100);
        // Last 32 KiB for save file.
        flash[0x80f8] = 0x02;
        flash[0x80f9] = 0x02;
        flash[0x80fa] = 0x02;
        flash[0x80fb] = 0x02;
        flash[0x80fc] = 0x02;
        flash[0x80fd] = 0x02;
        flash[0x80fe] = 0x03;
        flash[0x80ff] = 0x02;
    } else {
        return;
    }
    // Setup banks for the game.
    sys.bk_tab[0x5] = 0x20d;
    sys.bk_tab[0x6] = sys.bk_tab[0x05] + 1;
    sys.bk_tab[0x7] = sys.bk_tab[0x05] + 2;
    sys.bk_tab[0x8] = sys.bk_tab[0x05] + 3;
    sys.bk_tab[0x9] = 0x20d + (data >> 12);
    sys.bk_tab[0xa] = sys.bk_tab[0x09] + 1;
    sys.bk_tab[0xb] = sys.bk_tab[0x09] + 2;
    sys.bk_tab[0xc] = sys.bk_tab[0x09] + 3;
    for (int i = 0x05; i <= 0x0c; i += 1)
        mem_bs(i);
    mem_write(0x2029, 0x0d);
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

static void sys_hook()
{
    uint8_t op;
 _again:
    op = mem_read(sys.cpu->pc, false);
    if (op == 0x20) {
        uint16_t func = mem_read16(sys.cpu->pc + 1);
        // __banked_function_call
        if (func == 0xd2f6 && sys.bk_tab[0xd] == sys.bk_sys_d) {
            func = mem_read16(__addr_reg);
            switch (func) {
            case 0xe9c8:            /* FileCreat */
                // XXX: Clear unused file indexes to make room for saving.
                if (sys.bk_sys_d == 0x0ea8) { /* A4980 */
                    for (int i = 0xaf80; i < 0xb000; i += 1) {
                        if (sys.flash[0x8000 + i] == 0x00)
                            sys.flash[0x8000 + i] = 0xff;
                    }
                } else if (sys.bk_sys_d == 0x0e88) { /* A4988 */
                    for (int i = 0xbf80; i < 0xe000; i += 1) {
                        if (sys.flash[0x8000 + i] == 0x00)
                            sys.flash[0x8000 + i] = 0xff;
                    }
                }
                break;
            case 0x0e7c1:       /* SysGetKey */
                if (sys.ram[_KEYCODE] & 0x80) {
                    sys.cpu->ac = sys.ram[_KEYCODE] & 0x3f;
                    sys.ram[_KEYCODE] = 0;
                } else {
                    sys.cpu->ac = 0xff;
                }
                sys.cpu->pc += 3;
                goto _again;
            }
        }
    }
}

static uint32_t vrEmu6502Exec(VrEmu6502 *cpu, uint32_t cycles)
{
#define NEXT sys_hook(); goto *_table[mem_read(cpu->pc++, false)]
#define EXIT goto _exit
    static void *_table[0x100] = {
        &&_00, &&_01, &&_02, &&_03, &&_04, &&_05, &&_06, &&_07, &&_08, &&_09, &&_0a, &&_0b, &&_0c, &&_0d, &&_0e, &&_0f,
        &&_10, &&_11, &&_12, &&_13, &&_14, &&_15, &&_16, &&_17, &&_18, &&_19, &&_1a, &&_1b, &&_1c, &&_1d, &&_1e, &&_1f,
        &&_20, &&_21, &&_22, &&_23, &&_24, &&_25, &&_26, &&_27, &&_28, &&_29, &&_2a, &&_2b, &&_2c, &&_2d, &&_2e, &&_2f,
        &&_30, &&_31, &&_32, &&_33, &&_34, &&_35, &&_36, &&_37, &&_38, &&_39, &&_3a, &&_3b, &&_3c, &&_3d, &&_3e, &&_3f,
        &&_40, &&_41, &&_42, &&_43, &&_44, &&_45, &&_46, &&_47, &&_48, &&_49, &&_4a, &&_4b, &&_4c, &&_4d, &&_4e, &&_4f,
        &&_50, &&_51, &&_52, &&_53, &&_54, &&_55, &&_56, &&_57, &&_58, &&_59, &&_5a, &&_5b, &&_5c, &&_5d, &&_5e, &&_5f,
        &&_60, &&_61, &&_62, &&_63, &&_64, &&_65, &&_66, &&_67, &&_68, &&_69, &&_6a, &&_6b, &&_6c, &&_6d, &&_6e, &&_6f,
        &&_70, &&_71, &&_72, &&_73, &&_74, &&_75, &&_76, &&_77, &&_78, &&_79, &&_7a, &&_7b, &&_7c, &&_7d, &&_7e, &&_7f,
        &&_80, &&_81, &&_82, &&_83, &&_84, &&_85, &&_86, &&_87, &&_88, &&_89, &&_8a, &&_8b, &&_8c, &&_8d, &&_8e, &&_8f,
        &&_90, &&_91, &&_92, &&_93, &&_94, &&_95, &&_96, &&_97, &&_98, &&_99, &&_9a, &&_9b, &&_9c, &&_9d, &&_9e, &&_9f,
        &&_a0, &&_a1, &&_a2, &&_a3, &&_a4, &&_a5, &&_a6, &&_a7, &&_a8, &&_a9, &&_aa, &&_ab, &&_ac, &&_ad, &&_ae, &&_af,
        &&_b0, &&_b1, &&_b2, &&_b3, &&_b4, &&_b5, &&_b6, &&_b7, &&_b8, &&_b9, &&_ba, &&_bb, &&_bc, &&_bd, &&_be, &&_bf,
        &&_c0, &&_c1, &&_c2, &&_c3, &&_c4, &&_c5, &&_c6, &&_c7, &&_c8, &&_c9, &&_ca, &&_cb, &&_cc, &&_cd, &&_ce, &&_cf,
        &&_d0, &&_d1, &&_d2, &&_d3, &&_d4, &&_d5, &&_d6, &&_d7, &&_d8, &&_d9, &&_da, &&_db, &&_dc, &&_dd, &&_de, &&_df,
        &&_e0, &&_e1, &&_e2, &&_e3, &&_e4, &&_e5, &&_e6, &&_e7, &&_e8, &&_e9, &&_ea, &&_eb, &&_ec, &&_ed, &&_ee, &&_ef,
        &&_f0, &&_f1, &&_f2, &&_f3, &&_f4, &&_f5, &&_f6, &&_f7, &&_f8, &&_f9, &&_fa, &&_fb, &&_fc, &&_fd, &&_fe, &&_ff,
    };
    uint32_t count = 0;
_exit:
    if (count >= cycles)
        return count;
    else
        NEXT;
_00:
    // brk(cpu, imp);
    // count += 7;
    // Upon BRK, shutdown the game.
    count = cycles;
    sys.ram[_SYSCON] |= 0x08;
    sys.cpu->pc = _MACCTL;
    environ_cb(RETRO_ENVIRONMENT_SHUTDOWN, NULL);
    EXIT;
_01:
    ora(cpu, xin);
    count += 6;
    NEXT;
_02:
    ldd(cpu, imm);
    count += 2;
    NEXT;
_03:
    nop(cpu, imp);
    count += 1;
    NEXT;
_04:
    tsb(cpu, zp);
    count += 5;
    NEXT;
_05:
    ora(cpu, zp);
    count += 3;
    NEXT;
_06:
    asl(cpu, zp);
    count += 5;
    NEXT;
_07:
    rmb0(cpu, zp);
    count += 5;
    NEXT;
_08:
    php(cpu, imp);
    count += 3;
    NEXT;
_09:
    ora(cpu, imm);
    count += 2;
    NEXT;
_0a:
    asl(cpu, acc);
    count += 2;
    NEXT;
_0b:
    nop(cpu, imp);
    count += 1;
    NEXT;
_0c:
    tsb(cpu, ab);
    count += 6;
    NEXT;
_0d:
    ora(cpu, ab);
    count += 4;
    NEXT;
_0e:
    asl(cpu, ab);
    count += 6;
    NEXT;
_0f:
    bbr0(cpu, zp);
    count += 5;
    NEXT;
_10:
    bpl(cpu, rel);
    count += 2;
    NEXT;
_11:
    ora(cpu, yip);
    count += 5;
    NEXT;
_12:
    ora(cpu, zpi);
    count += 5;
    NEXT;
_13:
    nop(cpu, imp);
    count += 1;
    NEXT;
_14:
    trb(cpu, zp);
    count += 5;
    NEXT;
_15:
    ora(cpu, zpx);
    count += 4;
    NEXT;
_16:
    asl(cpu, zpx);
    count += 6;
    NEXT;
_17:
    rmb1(cpu, zp);
    count += 5;
    NEXT;
_18:
    clc(cpu, imp);
    count += 2;
    NEXT;
_19:
    ora(cpu, ayp);
    count += 4;
    NEXT;
_1a:
    inc(cpu, acc);
    count += 2;
    NEXT;
_1b:
    nop(cpu, imp);
    count += 1;
    NEXT;
_1c:
    trb(cpu, ab);
    count += 6;
    NEXT;
_1d:
    ora(cpu, axp);
    count += 4;
    NEXT;
_1e:
    asl(cpu, axp);
    count += 6;
    NEXT;
_1f:
    bbr1(cpu, zp);
    count += 5;
    NEXT;
_20:
    jsr(cpu, ab);
    count += 6;
    NEXT;
_21:
    and(cpu, xin);
    count += 6;
    NEXT;
_22:
    ldd(cpu, imm);
    count += 2;
    NEXT;
_23:
    nop(cpu, imp);
    count += 1;
    NEXT;
_24:
    bit(cpu, zp);
    count += 3;
    NEXT;
_25:
    and(cpu, zp);
    count += 3;
    NEXT;
_26:
    rol(cpu, zp);
    count += 5;
    NEXT;
_27:
    rmb2(cpu, zp);
    count += 5;
    NEXT;
_28:
    plp(cpu, imp);
    count += 4;
    NEXT;
_29:
    and(cpu, imm);
    count += 2;
    NEXT;
_2a:
    rol(cpu, acc);
    count += 2;
    NEXT;
_2b:
    nop(cpu, imp);
    count += 1;
    NEXT;
_2c:
    bit(cpu, ab);
    count += 4;
    NEXT;
_2d:
    and(cpu, ab);
    count += 4;
    NEXT;
_2e:
    rol(cpu, ab);
    count += 6;
    NEXT;
_2f:
    bbr2(cpu, zp);
    count += 5;
    NEXT;
_30:
    bmi(cpu, rel);
    count += 2;
    NEXT;
_31:
    and(cpu, yip);
    count += 5;
    NEXT;
_32:
    and(cpu, zpi);
    count += 5;
    NEXT;
_33:
    nop(cpu, imp);
    count += 1;
    NEXT;
_34:
    bit(cpu, zpx);
    count += 4;
    NEXT;
_35:
    and(cpu, zpx);
    count += 4;
    NEXT;
_36:
    rol(cpu, zpx);
    count += 6;
    NEXT;
_37:
    rmb3(cpu, zp);
    count += 5;
    NEXT;
_38:
    sec(cpu, imp);
    count += 2;
    NEXT;
_39:
    and(cpu, ayp);
    count += 4;
    NEXT;
_3a:
    dec(cpu, acc);
    count += 2;
    NEXT;
_3b:
    nop(cpu, imp);
    count += 1;
    NEXT;
_3c:
    bit(cpu, abx);
    count += 4;
    NEXT;
_3d:
    and(cpu, axp);
    count += 4;
    NEXT;
_3e:
    rol(cpu, axp);
    count += 6;
    NEXT;
_3f:
    bbr3(cpu, zp);
    count += 5;
    NEXT;
_40:
    rti(cpu, imp);
    count += 6;
    EXIT;
_41:
    eor(cpu, xin);
    count += 6;
    NEXT;
_42:
    ldd(cpu, imm);
    count += 2;
    NEXT;
_43:
    nop(cpu, imp);
    count += 1;
    NEXT;
_44:
    ldd(cpu, zp);
    count += 3;
    NEXT;
_45:
    eor(cpu, zp);
    count += 3;
    NEXT;
_46:
    lsr(cpu, zp);
    count += 5;
    NEXT;
_47:
    rmb4(cpu, zp);
    count += 5;
    NEXT;
_48:
    pha(cpu, imp);
    count += 3;
    NEXT;
_49:
    eor(cpu, imm);
    count += 2;
    NEXT;
_4a:
    lsr(cpu, acc);
    count += 2;
    NEXT;
_4b:
    nop(cpu, imp);
    count += 1;
    NEXT;
_4c:
    jmp(cpu, ab);
    count += 3;
    NEXT;
_4d:
    eor(cpu, ab);
    count += 4;
    NEXT;
_4e:
    lsr(cpu, ab);
    count += 6;
    NEXT;
_4f:
    bbr4(cpu, zp);
    count += 5;
    NEXT;
_50:
    bvc(cpu, rel);
    count += 2;
    NEXT;
_51:
    eor(cpu, yip);
    count += 5;
    NEXT;
_52:
    eor(cpu, zpi);
    count += 5;
    NEXT;
_53:
    nop(cpu, imp);
    count += 1;
    NEXT;
_54:
    ldd(cpu, zpx);
    count += 4;
    NEXT;
_55:
    eor(cpu, zpx);
    count += 4;
    NEXT;
_56:
    lsr(cpu, zpx);
    count += 6;
    NEXT;
_57:
    rmb5(cpu, zp);
    count += 5;
    NEXT;
_58:
    cli(cpu, imp);
    count += 2;
    NEXT;
_59:
    eor(cpu, ayp);
    count += 4;
    NEXT;
_5a:
    phy(cpu, imp);
    count += 3;
    NEXT;
_5b:
    nop(cpu, imp);
    count += 1;
    NEXT;
_5c:
    ldd(cpu, ab);
    count += 8;
    NEXT;
_5d:
    eor(cpu, axp);
    count += 4;
    NEXT;
_5e:
    lsr(cpu, axp);
    count += 6;
    NEXT;
_5f:
    bbr5(cpu, zp);
    count += 5;
    NEXT;
_60:
    rts(cpu, imp);
    count += 6;
    EXIT;
_61:
    adc(cpu, xin);
    count += 6;
    NEXT;
_62:
    ldd(cpu, imm);
    count += 2;
    NEXT;
_63:
    nop(cpu, imp);
    count += 1;
    NEXT;
_64:
    stz(cpu, zp);
    count += 3;
    NEXT;
_65:
    adc(cpu, zp);
    count += 3;
    NEXT;
_66:
    ror(cpu, zp);
    count += 5;
    NEXT;
_67:
    rmb6(cpu, zp);
    count += 5;
    NEXT;
_68:
    pla(cpu, imp);
    count += 4;
    NEXT;
_69:
    adc(cpu, imm);
    count += 2;
    NEXT;
_6a:
    ror(cpu, acc);
    count += 2;
    NEXT;
_6b:
    nop(cpu, imp);
    count += 1;
    NEXT;
_6c:
    jmp(cpu, ind);
    count += 6;
    NEXT;
_6d:
    adc(cpu, ab);
    count += 4;
    NEXT;
_6e:
    ror(cpu, ab);
    count += 6;
    NEXT;
_6f:
    bbr6(cpu, zp);
    count += 5;
    NEXT;
_70:
    bvs(cpu, rel);
    count += 2;
    NEXT;
_71:
    adc(cpu, yip);
    count += 5;
    NEXT;
_72:
    adc(cpu, zpi);
    count += 5;
    NEXT;
_73:
    nop(cpu, imp);
    count += 1;
    NEXT;
_74:
    stz(cpu, zpx);
    count += 4;
    NEXT;
_75:
    adc(cpu, zpx);
    count += 4;
    NEXT;
_76:
    ror(cpu, zpx);
    count += 6;
    NEXT;
_77:
    rmb7(cpu, zp);
    count += 5;
    NEXT;
_78:
    sei(cpu, imp);
    count += 2;
    NEXT;
_79:
    adc(cpu, ayp);
    count += 4;
    NEXT;
_7a:
    ply(cpu, imp);
    count += 4;
    NEXT;
_7b:
    nop(cpu, imp);
    count += 1;
    NEXT;
_7c:
    jmp(cpu, indx);
    count += 6;
    NEXT;
_7d:
    adc(cpu, axp);
    count += 4;
    NEXT;
_7e:
    ror(cpu, axp);
    count += 6;
    NEXT;
_7f:
    bbr7(cpu, zp);
    count += 5;
    NEXT;
_80:
    bra(cpu, rel);
    count += 2;
    NEXT;
_81:
    sta(cpu, xin);
    count += 6;
    NEXT;
_82:
    ldd(cpu, imm);
    count += 2;
    NEXT;
_83:
    nop(cpu, imp);
    count += 1;
    NEXT;
_84:
    sty(cpu, zp);
    count += 3;
    NEXT;
_85:
    sta(cpu, zp);
    count += 3;
    NEXT;
_86:
    stx(cpu, zp);
    count += 3;
    NEXT;
_87:
    smb0(cpu, zp);
    count += 5;
    NEXT;
_88:
    dey(cpu, imp);
    count += 2;
    NEXT;
_89:
    bit(cpu, imm);
    count += 2;
    NEXT;
_8a:
    txa(cpu, imp);
    count += 2;
    NEXT;
_8b:
    nop(cpu, imp);
    count += 1;
    NEXT;
_8c:
    sty(cpu, ab);
    count += 4;
    NEXT;
_8d:
    sta(cpu, ab);
    count += 4;
    NEXT;
_8e:
    stx(cpu, ab);
    count += 4;
    NEXT;
_8f:
    bbs0(cpu, zp);
    count += 5;
    NEXT;
_90:
    bcc(cpu, rel);
    count += 2;
    NEXT;
_91:
    sta(cpu, yin);
    count += 6;
    NEXT;
_92:
    sta(cpu, zpi);
    count += 5;
    NEXT;
_93:
    nop(cpu, imp);
    count += 1;
    NEXT;
_94:
    sty(cpu, zpx);
    count += 4;
    NEXT;
_95:
    sta(cpu, zpx);
    count += 4;
    NEXT;
_96:
    stx(cpu, zpy);
    count += 4;
    NEXT;
_97:
    smb1(cpu, zp);
    count += 5;
    NEXT;
_98:
    tya(cpu, imp);
    count += 2;
    NEXT;
_99:
    sta(cpu, aby);
    count += 5;
    NEXT;
_9a:
    txs(cpu, imp);
    count += 2;
    NEXT;
_9b:
    nop(cpu, imp);
    count += 1;
    NEXT;
_9c:
    stz(cpu, ab);
    count += 4;
    NEXT;
_9d:
    sta(cpu, abx);
    count += 5;
    NEXT;
_9e:
    stz(cpu, abx);
    count += 5;
    NEXT;
_9f:
    bbs1(cpu, zp);
    count += 5;
    NEXT;
_a0:
    ldy(cpu, imm);
    count += 2;
    NEXT;
_a1:
    lda(cpu, xin);
    count += 6;
    NEXT;
_a2:
    ldx(cpu, imm);
    count += 2;
    NEXT;
_a3:
    nop(cpu, imp);
    count += 1;
    NEXT;
_a4:
    ldy(cpu, zp);
    count += 3;
    NEXT;
_a5:
    lda(cpu, zp);
    count += 3;
    NEXT;
_a6:
    ldx(cpu, zp);
    count += 3;
    NEXT;
_a7:
    smb2(cpu, zp);
    count += 5;
    NEXT;
_a8:
    tay(cpu, imp);
    count += 2;
    NEXT;
_a9:
    lda(cpu, imm);
    count += 2;
    NEXT;
_aa:
    tax(cpu, imp);
    count += 2;
    NEXT;
_ab:
    nop(cpu, imp);
    count += 1;
    NEXT;
_ac:
    ldy(cpu, ab);
    count += 4;
    NEXT;
_ad:
    lda(cpu, ab);
    count += 4;
    NEXT;
_ae:
    ldx(cpu, ab);
    count += 4;
    NEXT;
_af:
    bbs2(cpu, zp);
    count += 5;
    NEXT;
_b0:
    bcs(cpu, rel);
    count += 2;
    NEXT;
_b1:
    lda(cpu, yip);
    count += 5;
    NEXT;
_b2:
    lda(cpu, zpi);
    count += 5;
    NEXT;
_b3:
    nop(cpu, imp);
    count += 1;
    NEXT;
_b4:
    ldy(cpu, zpx);
    count += 4;
    NEXT;
_b5:
    lda(cpu, zpx);
    count += 4;
    NEXT;
_b6:
    ldx(cpu, zpy);
    count += 4;
    NEXT;
_b7:
    smb3(cpu, zp);
    count += 5;
    NEXT;
_b8:
    clv(cpu, imp);
    count += 2;
    NEXT;
_b9:
    lda(cpu, ayp);
    count += 4;
    NEXT;
_ba:
    tsx(cpu, imp);
    count += 2;
    NEXT;
_bb:
    nop(cpu, imp);
    count += 1;
    NEXT;
_bc:
    ldy(cpu, axp);
    count += 4;
    NEXT;
_bd:
    lda(cpu, axp);
    count += 4;
    NEXT;
_be:
    ldx(cpu, ayp);
    count += 4;
    NEXT;
_bf:
    bbs3(cpu, zp);
    count += 5;
    NEXT;
_c0:
    cpy(cpu, imm);
    count += 2;
    NEXT;
_c1:
    cmp(cpu, xin);
    count += 6;
    NEXT;
_c2:
    ldd(cpu, imm);
    count += 2;
    NEXT;
_c3:
    nop(cpu, imp);
    count += 1;
    NEXT;
_c4:
    cpy(cpu, zp);
    count += 3;
    NEXT;
_c5:
    cmp(cpu, zp);
    count += 3;
    NEXT;
_c6:
    dec(cpu, zp);
    count += 5;
    NEXT;
_c7:
    smb4(cpu, zp);
    count += 5;
    NEXT;
_c8:
    iny(cpu, imp);
    count += 2;
    NEXT;
_c9:
    cmp(cpu, imm);
    count += 2;
    NEXT;
_ca:
    dex(cpu, imp);
    count += 2;
    NEXT;
_cb:
    wai(cpu, imp);
    count += 3;
    NEXT;
_cc:
    cpy(cpu, ab);
    count += 4;
    NEXT;
_cd:
    cmp(cpu, ab);
    count += 4;
    NEXT;
_ce:
    dec(cpu, ab);
    count += 6;
    NEXT;
_cf:
    bbs4(cpu, zp);
    count += 5;
    NEXT;
_d0:
    bne(cpu, rel);
    count += 2;
    NEXT;
_d1:
    cmp(cpu, yip);
    count += 5;
    NEXT;
_d2:
    cmp(cpu, zpi);
    count += 5;
    NEXT;
_d3:
    nop(cpu, imp);
    count += 1;
    NEXT;
_d4:
    ldd(cpu, zpx);
    count += 4;
    NEXT;
_d5:
    cmp(cpu, zpx);
    count += 4;
    NEXT;
_d6:
    dec(cpu, zpx);
    count += 6;
    NEXT;
_d7:
    smb5(cpu, zp);
    count += 5;
    NEXT;
_d8:
    cld(cpu, imp);
    count += 2;
    NEXT;
_d9:
    cmp(cpu, ayp);
    count += 4;
    NEXT;
_da:
    phx(cpu, imp);
    count += 3;
    NEXT;
_db:
    stp(cpu, imp);
    count += 3;
    NEXT;
_dc:
    ldd(cpu, ab);
    count += 4;
    NEXT;
_dd:
    cmp(cpu, axp);
    count += 4;
    NEXT;
_de:
    dec(cpu, abx);
    count += 7;
    NEXT;
_df:
    bbs5(cpu, zp);
    count += 5;
    NEXT;
_e0:
    cpx(cpu, imm);
    count += 2;
    NEXT;
_e1:
    sbc(cpu, xin);
    count += 6;
    NEXT;
_e2:
    ldd(cpu, imm);
    count += 2;
    NEXT;
_e3:
    nop(cpu, imp);
    count += 1;
    NEXT;
_e4:
    cpx(cpu, zp);
    count += 3;
    NEXT;
_e5:
    sbc(cpu, zp);
    count += 3;
    NEXT;
_e6:
    inc(cpu, zp);
    count += 5;
    NEXT;
_e7:
    smb6(cpu, zp);
    count += 5;
    NEXT;
_e8:
    inx(cpu, imp);
    count += 2;
    NEXT;
_e9:
    sbc(cpu, imm);
    count += 2;
    NEXT;
_ea:
    nop(cpu, imp);
    count += 2;
    NEXT;
_eb:
    nop(cpu, imp);
    count += 1;
    NEXT;
_ec:
    cpx(cpu, ab);
    count += 4;
    NEXT;
_ed:
    sbc(cpu, ab);
    count += 4;
    NEXT;
_ee:
    inc(cpu, ab);
    count += 6;
    NEXT;
_ef:
    bbs6(cpu, zp);
    count += 5;
    NEXT;
_f0:
    beq(cpu, rel);
    count += 2;
    NEXT;
_f1:
    sbc(cpu, yip);
    count += 5;
    NEXT;
_f2:
    sbc(cpu, zpi);
    count += 5;
    NEXT;
_f3:
    nop(cpu, imp);
    count += 1;
    NEXT;
_f4:
    ldd(cpu, zpx);
    count += 4;
    NEXT;
_f5:
    sbc(cpu, zpx);
    count += 4;
    NEXT;
_f6:
    inc(cpu, zpx);
    count += 6;
    NEXT;
_f7:
    smb7(cpu, zp);
    count += 5;
    NEXT;
_f8:
    sed(cpu, imp);
    count += 2;
    NEXT;
_f9:
    sbc(cpu, ayp);
    count += 4;
    NEXT;
_fa:
    plx(cpu, imp);
    count += 4;
    NEXT;
_fb:
    nop(cpu, imp);
    count += 1;
    NEXT;
_fc:
    ldd(cpu, ab);
    count += 4;
    NEXT;
_fd:
    sbc(cpu, axp);
    count += 4;
    NEXT;
_fe:
    inc(cpu, abx);
    count += 7;
    NEXT;
_ff:
    bbs7(cpu, zp);
    count += 5;
    NEXT;
}

static void sys_step()
{
    uint32_t cycles = 0;
    while (cycles < 0x12000 * vars.cpu_rate) {
        if (sys.ram[_SYSCON] & 0x08) {
            cycles += 400 * vars.cpu_rate;
        } else {
            for (int i = 0; i < vars.cpu_rate; i += 1) {
                // XXX: 400 cycles seems to be a safe value for SysHalt handling..
                cycles += vrEmu6502Exec(sys.cpu, 400);
                if (sys.ram[_SYSCON] & 0x08)
                    break;
            }
        }
        sys_timer(vars.timer_rate);
        sys_isr();
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
}

void retro_set_environment(retro_environment_t cb)
{
    static struct retro_core_option_definition opts[] = {
        {
            .key = "gam4980_lcd_color",
            .desc = "LCD color theme",
            .values = {{"grey"}, {"green"}, {"blue"}, {"yellow"}, {NULL}},
            .default_value = "grey",
        },
        {
            .key = "gam4980_cpu_rate",
            .desc = "CPU clock rate",
            .values = {{"1"}, {"2"}, {"3"}, {"4"}, {"5"}, {"6"}, {"7"}, {"8"}, {NULL}},
            .default_value = "1",
        },
        {
            .key = "gam4980_timer_rate",
            .desc = "Timer clock rate",
            .values = {{"1"}, {"2"}, {"3"}, {"4"}, {"5"}, {"6"}, {"7"}, {"8"}, {NULL}},
            .default_value = "1",
        },
        { NULL, NULL, NULL, {{0}}, NULL },
    };
    static struct retro_input_descriptor inputs[] = {
        { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_B, "EXIT" },
        { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_Y, "HELP" },
        { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_SELECT, "INSERT" },
        { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_START, "SEARCH" },
        { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_UP, "UP" },
        { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_DOWN, "DOWN" },
        { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_LEFT, "LEFT" },
        { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_RIGHT, "RIGHT" },
        { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_A, "ENTER" },
        { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_X, "R" },
        { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_L, "PGUP" },
        { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_R, "PGDN" },
        { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_L2, "MODIFY" },
        { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_R2, "DEL" },
        { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_L3, "A" },
        { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_R3, "Z" },
        { 0, 0, 0, 0, NULL },
    };

    static struct retro_log_callback log;
    static struct retro_keyboard_callback kbd = {
        .callback = keyboard_cb,
    };
    static struct retro_frame_time_callback frame = {
        .callback = frame_cb,
        .reference = 1000000 / 60,
    };
    static bool yes = true;
    environ_cb = cb;
    if (environ_cb(RETRO_ENVIRONMENT_GET_LOG_INTERFACE, &log))
        log_cb = log.log;
    environ_cb(RETRO_ENVIRONMENT_SET_FRAME_TIME_CALLBACK, &frame);
    environ_cb(RETRO_ENVIRONMENT_SET_KEYBOARD_CALLBACK, &kbd);
    environ_cb(RETRO_ENVIRONMENT_SET_SUPPORT_NO_GAME, &yes);

    unsigned opts_ver = 0;
    environ_cb(RETRO_ENVIRONMENT_GET_CORE_OPTIONS_VERSION, &opts_ver);
    if (opts_ver >= 1) {
        environ_cb(RETRO_ENVIRONMENT_SET_CORE_OPTIONS, &opts);
    }
    environ_cb(RETRO_ENVIRONMENT_SET_INPUT_DESCRIPTORS, &inputs);
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

static void apply_variables()
{
    struct retro_variable var = {0};

    var.key = "gam4980_lcd_color";
    if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var)) {
        if (strcmp(var.value, "grey") == 0) {
            vars.lcd_bg = 0xd6da;
            vars.lcd_fg = 0x0000;
        } else if (strcmp(var.value, "green") == 0) {
            vars.lcd_bg = 0x96e1;
            vars.lcd_fg = 0x0882;
        } else if (strcmp(var.value, "blue") == 0) {
            vars.lcd_bg = 0x3edd;
            vars.lcd_fg = 0x09a8;
        } else if (strcmp(var.value, "yellow") == 0) {
            vars.lcd_bg = 0xf72c;
            vars.lcd_fg = 0x2920;
        }
    }
    var.key = "gam4980_cpu_rate";
    if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var))
        vars.cpu_rate = atoi(var.value);

    var.key = "gam4980_timer_rate";
    if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var))
        vars.timer_rate = atoi(var.value);
}

void retro_init(void)
{
    char *systemdir;
    char romdir[512];
    environ_cb(RETRO_ENVIRONMENT_GET_SYSTEM_DIRECTORY, &systemdir);
    snprintf(romdir, 512, "%s/gam4980", systemdir);
    sys_init(romdir);
    apply_variables();
}

bool retro_load_game(const struct retro_game_info *game)
{
    if (game == NULL)
        return true;
    if (game->data == NULL)
        return false;
    if (game->size > 0x1e0000) {
        // Game too large! (>1920K)
        return false;
    }
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
        fb[y * LCD_WIDTH + x * 8 + i] = p ? vars.lcd_fg : vars.lcd_bg;
    }
}


void retro_run(void)
{
    bool vupdated = false;
    if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE_UPDATE, &vupdated) && vupdated)
        apply_variables();

    input_poll_cb();

    // Handle joypad.
    static int pressed = -1;
    static int repeat = 0;
    for (int i = 0; i < 16; i += 1) {
        if (pressed == i) {
            if (input_state_cb(0, RETRO_DEVICE_JOYPAD, 0, i) == 0) {
                pressed = -1;
                repeat = 0;
            } else {
                repeat += 1;
                if (repeat > 20) {
                    repeat -= 5;
                    sys_keydown(_joyk[i]);
                }
            }
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
    switch (id) {
    case RETRO_MEMORY_SAVE_RAM:
        return sys.flash;
    default:
        return NULL;
    }
}

size_t retro_get_memory_size(unsigned id)
{
    switch (id) {
    case RETRO_MEMORY_SAVE_RAM:
        // Saved: $000000-$00bfff, $1f8000-$1fffff
        return 0x14000;
    default:
        return 0;
    }
}
