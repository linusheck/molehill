cmake_minimum_required(VERSION 3.15)
project(fastmole LANGUAGES CXX)

# Set the C++ standard
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

option(STORMPY_DISABLE_SIGNATURE_DOC "Disable the signature in the documentation" OFF)
MARK_AS_ADVANCED(STORMPY_DISABLE_SIGNATURE_DOC)
set(PYBIND_VERSION "" CACHE STRING "Pybind11 version to use")
MARK_AS_ADVANCED(PYBIND_VERSION)
set(STORM_DIR_HINT "" CACHE STRING "A hint where the Storm library can be found.")

#+
if (DEFINED DISABLE_SMG)
    add_definitions(-DDISABLE_SMG)
endif()

find_package(storm REQUIRED HINTS ${STORM_DIR_HINT})

find_package(Python COMPONENTS Interpreter Development REQUIRED)
# we got the version from build.py
include(cmake/include_pybind11.cmake)

set(CMAKE_CXX_STANDARD 20)

# This sets interprocedural optimization off as this leads to some problems on some systems
set(CMAKE_INTERPROCEDURAL_OPTIMIZATION OFF)
# This sets the default visibility from hidden to default,
# which is recommended *not* to do, but leads to errors otherwise.
set(CMAKE_CXX_VISIBILITY_PRESET "default")

# Set configurations
set(STORM_VERSION ${storm_VERSION})
# Set number types from Carl
# set_variable_string(STORM_USE_CLN_EA_BOOL ${STORM_USE_CLN_EA})
# set_variable_string(STORM_USE_CLN_RF_BOOL ${STORM_USE_CLN_RF})
# if (STORM_USE_CLN_EA)
#     set(PYCARL_EA_PACKAGE "cln")
# else()
#     set(PYCARL_EA_PACKAGE "gmp")
# endif()
# if (STORM_USE_CLN_RF)
#     set(PYCARL_RF_PACKAGE "cln")
# else()
#     set(PYCARL_RF_PACKAGE "gmp")
# endif()
# set(PYCARL_IMPORTS "import pycarl")
# if (STORM_USE_CLN_EA OR STORM_USE_CLN_RF)
#     set(PYCARL_IMPORTS "${PYCARL_IMPORTS}\nimport pycarl.cln")
# endif()
# if (NOT STORM_USE_CLN_EA OR NOT STORM_USE_CLN_RF)
#     set(PYCARL_IMPORTS "${PYCARL_IMPORTS}\nimport pycarl.gmp")
# endif()

# Add the module
file(GLOB_RECURSE FASTMOLE_SOURCES "fastmole/src/*.cpp" "fastmole/src/*.h")
pybind11_add_module(fastmole ${FASTMOLE_SOURCES})

# Link Storm library
target_link_libraries(fastmole PRIVATE storm)
