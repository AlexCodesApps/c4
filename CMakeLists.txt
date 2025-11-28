cmake_minimum_required(VERSION 3.10)
project(c4)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(CMAKE_C_STANDARD 11)
set(CMAKE_C_STANDARD_REQUIRED TRUE)
add_executable(c4 main.c
	src/debug.c src/lexer.c src/str.c src/arena.c src/parser.c
	src/ast.c src/dir_walker.c src/i128.c src/fmt.c src/type.c
	src/graph.c src/sema.c src/common.c src/vm.c src/eval.c)

if(CMAKE_C_COMPILER_ID STREQUAL "GNU" AND CMAKE_BUILD_TYPE STREQUAL "Debug")
	target_compile_options(c4 PRIVATE -D_GLIBCXX_DEBUG)
endif()

if (CMAKE_C_COMPILER_ID MATCHES "Clang|GNU")
	target_compile_options(c4 PRIVATE -Wall -Wextra -Wpedantic -Wimplicit-fallthrough -Wconversion)
	if(CMAKE_BUILD_TYPE STREQUAL "Debug")
		add_compile_definitions(c4 PRIVATE C4_DEBUG)
		target_compile_options(c4 PRIVATE -fsanitize=address)
		target_link_options(c4 PRIVATE -fsanitize=address)
	else()
		target_link_options(c4 PRIVATE -flto)
	endif()
elseif (CMAKE_C_COMPILER_ID STREQUAL "MSVC")
    target_compile_options(c4 PRIVATE /W4 /permissive-)
endif()
