cmake_minimum_required(VERSION 3.15)
project(fastmole LANGUAGES CXX)

include(${CMAKE_CURRENT_SOURCE_DIR}/cmake/macros.cmake)

# Set the C++ standard
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

option(STORMPY_DISABLE_SIGNATURE_DOC "Disable the signature in the documentation" OFF)
MARK_AS_ADVANCED(STORMPY_DISABLE_SIGNATURE_DOC)
set(PYBIND_VERSION "" CACHE STRING "Pybind11 version to use")
MARK_AS_ADVANCED(PYBIND_VERSION)
set(STORM_DIR_HINT "" CACHE STRING "A hint where the Storm library can be found.")
option(ALLOW_STORM_SYSTEM "Allow finding a storm version on the system" ON)
option(ALLOW_STORM_FETCH "Allow fetching storm" ON)
set(STORM_GIT_REPO "" CACHE STRING  "Git repo used for fetching storm")
set(STORM_GIT_TAG "" CACHE STRING "Git repo tag used for fetching storm")

# Query stormpy.info to determine Storm configuration
execute_process(
    COMMAND "${Python_EXECUTABLE}" -c "import stormpy.info; print(stormpy.info.storm_from_system())"
    RESULT_VARIABLE _stormpy_result
    OUTPUT_VARIABLE STORMPY_FROM_SYSTEM
    ERROR_VARIABLE _stormpy_error
    OUTPUT_STRIP_TRAILING_WHITESPACE
)

if(NOT _stormpy_result EQUAL 0)
    message(FATAL_ERROR "molehill - Failed to query stormpy.info.storm_from_system(): ${_stormpy_error}")
endif()

# Configure Storm settings based on stormpy configuration
if(STORMPY_FROM_SYSTEM STREQUAL "True")
    execute_process(
        COMMAND "${Python_EXECUTABLE}" -c "import stormpy.info; print(stormpy.info.storm_directory())"
        RESULT_VARIABLE _directory_result
        OUTPUT_VARIABLE STORM_DIRECTORY_INFO
        ERROR_VARIABLE _origin_error
        OUTPUT_STRIP_TRAILING_WHITESPACE
    )

    if(NOT _directory_result EQUAL 0)
        message(FATAL_ERROR "molehill - Failed to query stormpy.info.storm_directory(): ${_origin_error}")
    endif()

    message(STATUS "molehill - StormPy uses system Storm from: ${STORM_DIRECTORY_INFO} - configuring molehill to use the same system Storm")

    set(STORM_DIR_HINT "${STORM_DIRECTORY_INFO}")
    set(ALLOW_STORM_SYSTEM ON)
    set(ALLOW_STORM_FETCH OFF)
else()
    message(STATUS "molehill - StormPy uses fetched Storm - querying Storm origin information")

    # Get Storm origin information
    execute_process(
        COMMAND "${Python_EXECUTABLE}" -c "import stormpy.info; repo, tag = stormpy.info.storm_origin_info(); print(f'{repo or \"\"};{tag or \"\"}')"
        RESULT_VARIABLE _origin_result
        OUTPUT_VARIABLE STORM_ORIGIN_INFO
        ERROR_VARIABLE _origin_error
        OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    
    if(NOT _origin_result EQUAL 0)
        message(FATAL_ERROR "molehill - Failed to query stormpy.info.storm_origin_info(): ${_origin_error}")
    endif()
    
    # Parse repo and tag
    list(GET STORM_ORIGIN_INFO 0 STORM_ORIGIN_REPO)
    list(GET STORM_ORIGIN_INFO 1 STORM_ORIGIN_TAG)
    
    message(STATUS "molehill - Storm origin repo: ${STORM_ORIGIN_REPO}")
    message(STATUS "molehill - Storm origin tag: ${STORM_ORIGIN_TAG}")
    
    # Configure to fetch the same Storm version as stormpy
    set(ALLOW_STORM_SYSTEM OFF)
    set(ALLOW_STORM_FETCH ON)
    
    if(NOT STORM_ORIGIN_REPO STREQUAL "")
        set(STORM_GIT_REPO "${STORM_ORIGIN_REPO}")
    else()
        message(FATAL_ERROR "molehill - Failed to determine Storm origin repository")
    endif()
    
    if(NOT STORM_ORIGIN_TAG STREQUAL "")
        set(STORM_GIT_TAG "${STORM_ORIGIN_TAG}")
    else()
        message(FATAL_ERROR "molehill - Failed to determine Storm origin tag")
    endif()
    
    message(STATUS "molehill - Configured to fetch Storm from: ${STORM_GIT_REPO} (tag: ${STORM_GIT_TAG})")
endif()

# Check whether inputs are sane.
if (NOT ALLOW_STORM_SYSTEM AND NOT ALLOW_STORM_FETCH)
    message(FATAL_ERROR "molehill - Storm must be either fetched or used from system, yet ALLOW_STORM_SYSTEM=OFF and ALLOW_STORM_FETCH=OFF was set.")
endif()

if (DEFINED DISABLE_SMG)
    add_definitions(-DDISABLE_SMG)
endif()

find_package(pybind11 CONFIG REQUIRED)
message(STATUS "molehill - Using pybind11 version ${pybind11_VERSION}")

function(check_hint NAME DIR_FOUND HINT_DIR FOUND_VERSION)
    # Get absolute path
    get_filename_component(PATH_FOUND ${DIR_FOUND} ABSOLUTE)
    # Print path
    if (NOT "${FOUND_VERSION}" STREQUAL "")
        message(STATUS "molehill - Using ${NAME} version ${FOUND_VERSION} from ${PATH_FOUND}")
    else()
        message(STATUS "molehill - Using ${NAME} from ${PATH_FOUND}")
    endif()

    # Check that hint was used
    if (NOT "${HINT_DIR}" STREQUAL "")
        get_filename_component(PATH_HINT ${HINT_DIR} ABSOLUTE)
        if (NOT "${PATH_FOUND}" STREQUAL "${PATH_HINT}")
            MESSAGE(SEND_ERROR "molehill - Using different ${NAME} directory ${PATH_FOUND} instead of given ${PATH_HINT}!")
        endif()
    endif()
endfunction(check_hint)

if(ALLOW_STORM_SYSTEM)
    set(STORM_MIN_VERSION "1.11.0")
    if (ALLOW_STORM_FETCH)
        find_package(storm HINTS ${STORM_DIR_HINT}) # NOT REQUIRED, can be fetched.
    else()
        find_package(storm REQUIRED HINTS ${STORM_DIR_HINT}) # REQUIRED, cannot be fetched.
    endif()
    check_hint("Storm" ${storm_DIR} "${STORM_DIR_HINT}" ${storm_VERSION})
    # Check Storm version
    if (${storm_VERSION} VERSION_LESS ${STORM_MIN_VERSION})
        MESSAGE(FATAL_ERROR "molehill - Storm version ${storm_VERSION} from ${storm_DIR} is not supported anymore!\nmolehill requires at least Storm version >= ${STORM_MIN_VERSION}.")
    endif()

    message(WARNING "molehill - When using system version of Storm, it's up to the user to ensure StormPy was built against the same version!")

    set(STORM_FROM_SYSTEM TRUE)
    get_filename_component(STORM_DIR_PATH ${storm_DIR} ABSOLUTE)
    set(STORM_DIR "\"${STORM_DIR_PATH}\"")

    # Set dependency variables
    set_dependency_var(SPOT)
    set_dependency_var(XERCES)
    # Check for optional Storm libraries
    storm_with_lib(DFT)
    storm_with_lib(GSPN)
    storm_with_lib(PARS)
    storm_with_lib(POMDP)
endif ()
if (NOT storm_FOUND AND ALLOW_STORM_FETCH)
    include(FetchContent)
    SET(FETCHCONTENT_QUIET OFF)
    SET(STORM_BUILD_EXECUTABLES OFF)
    FetchContent_Declare(
            storm
            GIT_REPOSITORY ${STORM_GIT_REPO}
            GIT_TAG        ${STORM_GIT_TAG}
    )
    FETCHCONTENT_MAKEAVAILABLE(storm)
    include(${storm_BINARY_DIR}/stormOptions.cmake)
    set(HAVE_STORM_DFT TRUE)
    set(HAVE_STORM_GSPN TRUE)
    set(HAVE_STORM_PARS TRUE)
    set(HAVE_STORM_POMDP TRUE)
    # Set dependency variables
    set_dependency_var(SPOT)
    set_dependency_var(XERCES)
    if (FETCHCONTENT_SOURCE_DIR_storm)
        # We are setting the Storm source to be something local from the outside.
        set(STORM_FETCHED_FROM_REPO ${FETCHCONTENT_SOURCE_DIR_storm})
        set(STORM_FETCHED_FROM_TAG "__local-source-dir__")
    else()
        set(STORM_FETCHED_FROM_REPO ${STORM_GIT_REPO})
        set(STORM_FETCHED_FROM_TAG ${STORM_GIT_TAG})
    endif()
    set(STORM_FROM_SYSTEM FALSE)
    set(STORM_DIR "None")
endif()

# This sets interprocedural optimization off as this leads to some problems on some systems
set(CMAKE_INTERPROCEDURAL_OPTIMIZATION OFF)
# This sets the default visibility from hidden to default,
# which is recommended *not* to do, but leads to errors otherwise.
set(CMAKE_CXX_VISIBILITY_PRESET "default")

# Add the module
file(GLOB_RECURSE FASTMOLE_SOURCES "fastmole/src/*.cpp" "fastmole/src/*.h")
pybind11_add_module(fastmole ${FASTMOLE_SOURCES})

# Link Storm library
target_link_libraries(fastmole PRIVATE storm)

# Place the built extension in the Python package directory
set_target_properties(fastmole PROPERTIES
    LIBRARY_OUTPUT_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/molehill"
)

install(TARGETS fastmole DESTINATION molehill)
