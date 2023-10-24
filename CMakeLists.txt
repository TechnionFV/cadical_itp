project(Cadical)
cmake_minimum_required(VERSION 3.5.0)

if (CMAKE_SOURCE_DIR STREQUAL CMAKE_BINARY_DIR ) 
  message (FATAL_ERROR
    "In-source builds are not allowed. Please clean your source tree and try again.")  
endif()

# # Add path for custom modules
# set(CMAKE_MODULE_PATH
#   ${CMAKE_MODULE_PATH}
#   "${CMAKE_CURRENT_SOURCE_DIR}/cmake"
#   )

set (CMAKE_CXX_STANDARD 11)

if(NOT EXISTS "${CMAKE_CURRENT_BINARY_DIR}/build.hpp")
  execute_process(COMMAND cat ${CMAKE_SOURCE_DIR}/VERSION OUTPUT_VARIABLE VERSION)
  string(REGEX REPLACE "\n$" "" VERSION "${VERSION}")
  execute_process(COMMAND ${CMAKE_SOURCE_DIR}/scripts/get-git-id.sh OUTPUT_VARIABLE IDENTIFIER)
  string(REGEX REPLACE "\n$" "" IDENTIFIER "${IDENTIFIER}")
  string(TIMESTAMP TODAY "%Y.%m.%d")
#    execute_process( COMMAND 
#           ${CMAKE_CURRENT_SOURCE_DIR}/scripts/make-build-header.sh > build.hpp
#           WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR})
  file (WRITE "${CMAKE_CURRENT_BINARY_DIR}/build.hpp" "#define VERSION \"${VERSION}\"\n")
  file (APPEND "${CMAKE_CURRENT_BINARY_DIR}/build.hpp" "#define IDENTIFIER \"${IDENTIFIER}\"\n")
  file (APPEND "${CMAKE_CURRENT_BINARY_DIR}/build.hpp" "#define COMPILER \"${CMAKE_CXX_COMPILER_VERSION}\"\n")
  file (APPEND "${CMAKE_CURRENT_BINARY_DIR}/build.hpp" "#define FLAGS \"${CMAKE_CXX_FLAGS}\"\n")
  file (APPEND "${CMAKE_CURRENT_BINARY_DIR}/build.hpp" "#define DATE \"${TODAY}\"\n")
endif()

add_custom_command(
    OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/build.hpp
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/scripts/
    COMMAND make-build-header.sh
    DEPENDS cadical.LIB
)

# check for rt lib. Not needed on OSX.
find_library(RT_LIB NAMES rt)
if (NOT RT_LIB)
  set(RT_LIB "")
endif()
mark_as_advanced(RT_LIB)

# prefer linking with static libraries
set(CMAKE_FIND_LIBRARY_SUFFIXES ".a" ${CMAKE_FIND_LIBRARY_SUFFIXES})

#include ("cmake/PackageOptions.cmake")

include_directories(
  ${CMAKE_CURRENT_BINARY_DIR}/src
  ${CMAKE_CURRENT_BINARY_DIR}
  )


add_subdirectory(src)

add_library(cadical.LIB STATIC
  $<TARGET_OBJECTS:cadical_src>)

set_target_properties(cadical.LIB 
  PROPERTIES OUTPUT_NAME "cadical")

add_executable (cadical src/cadical.cpp)
add_executable (mobical src/mobical.cpp)
target_link_libraries (cadical cadical.LIB)
target_link_libraries (mobical cadical.LIB)

install (TARGETS cadical.LIB cadical
  RUNTIME DESTINATION bin
  ARCHIVE DESTINATION lib)
