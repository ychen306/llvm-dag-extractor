cmake_minimum_required(VERSION 3.4)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

find_package(LLVM REQUIRED CONFIG)
message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(LLVM_BUILD_TOOLS ON)

add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})
add_definitions(-fno-rtti)

set(SRC
  extract.cpp)

llvm_map_components_to_libnames(LLVM_LIBRARIES support core)
add_library(DAGExtractor MODULE ${SRC})

if(APPLE)
  set_target_properties(DAGExtractor PROPERTIES LINK_FLAGS "-undefined dynamic_lookup")
endif(APPLE)
