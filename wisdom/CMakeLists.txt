# -----------------------------------------------------------------------------
# Project Setup

# NOTE: need CMake 3.9+ to specify project description:
#   https://cmake.org/cmake/help/latest/release/3.9.html?highlight=project%20description#commands
cmake_minimum_required(VERSION 3.9)
project(ExampleCMakeProject
    VERSION 0.1
    DESCRIPTION "Noodling around")

# -----------------------------------------------------------------------------
# Dependencies

# The version number "7.0" means "7.0 or higher".  CMake does not have a
# declarative way to specify complex version ranges (e.g. "7.0 or higher but
# not 7.13"), but I believe you can write manual checks for that kind of thing.
find_package(CURL 7.0 REQUIRED)

# Check for things you plan to use that might or might not be present in the
# standard library.
# See:
#   https://cmake.org/cmake/help/v3.9/module/CheckSymbolExists.html
#   https://cmake.org/cmake/help/v3.9/module/CheckIncludeFile.html
#   https://cmake.org/cmake/help/v3.9/module/CheckIncludeFileCXX.html
include(CheckSymbolExists)
check_symbol_exists(F_FULLFSYNC fcntl.h HAVE_F_FULLFSYNC)
include(CheckIncludeFileCXX)
check_include_file_cxx(atomic HAVE_ATOMIC)

# -----------------------------------------------------------------------------
# Shared library

add_library(example-lib SHARED
    lib/include/header.h
    lib/impl.c)

# CMake does not allow us to have two targets with the same name---even though
# if they did, the executable would be named "[name]" and the library would be
# named "lib[name].so" or "lib[name].dylib", so there is no clash.  This line
# sets the library's output name so that our outputs are "example" and
# "libexample.suffix".
set_target_properties(example-lib PROPERTIES OUTPUT_NAME example)

# Irritatingly, CMake does not have a single property for public headers.  We
# need to declare the public headers in two different ways.  The first way (via
# target_include_directories) informs CMake that any target in this project
# that depends on this library needs these included files.  The second way (via
# set_target_properties) informs CMake that these headers should be installed
# at install time.  See also "install(... PUBLIC_HEADER ...)" below.
target_include_directories(example-lib PUBLIC lib/include)
set_target_properties(example-lib PROPERTIES PUBLIC_HEADER lib/include/example.h)

# The library needs CURL at link-time.
# PRIVATE - targets that use example-lib do not also get all of CURL's symbols;
#   they need to explicitly link to CURL for that.
# PUBLIC - this library uses CURL and targets that use this library get CURL's
#   symbols through this library as well.
# INTERFACE - this library does not use curl, but targets that use this library
#   get CURL's symbols through this library.
target_link_libraries(example-lib PRIVATE CURL)

# -----------------------------------------------------------------------------
# Executable

add_executable(example
    app/main.c)

# NOTE: I am not sure what PRIVATE/PUBLIC/INTERFACE does for executables.
# Shouldn't all of an executable's symbols be private except for main?  I am
# fairly sure that PRIVATE is always the right choice here.
target_link_libraries(example PRIVATE example-lib)

# -----------------------------------------------------------------------------
# Install  (I feel that this should be automatic given just the list of
# targets, but CMake requires us to explicitly list the things we want
# installed.)

install(TARGETS example-lib example
    RUNTIME       DESTINATION ${CMAKE_INSTALL_BINDIR}
    LIBRARY       DESTINATION ${CMAKE_INSTALL_LIBDIR}
    PUBLIC_HEADER DESTINATION ${CMAKE_INSTALL_INCLUDEDIR})
