cmake_minimum_required(VERSION 3.9)
project(gam4980-libretro C)


option(LIBRETRO_STATIC "Statically link the libretro core" OFF)

if (LIBRETRO_STATIC)
  add_library(gam4980_libretro STATIC libretro.c)
else ()
  add_library(gam4980_libretro SHARED libretro.c)
endif ()

# Follow naming conventions for libretro cores
set_target_properties(gam4980_libretro PROPERTIES PREFIX "")
