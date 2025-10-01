#pragma once

#include "str.h"
#include <stdio.h>

#define BREAKPOINT()                                                           \
	asm("int3\n"                                                               \
		"nop\n") // not portable but program is borked anyways

typedef enum {
	DEBUG_LOG,
	DEBUG_ERROR,
} DebugLevel;

#define DEBUG_LEVEL_COUNT DEBUG_ERROR + 1

void va_debug(DebugLevel level, const char * filename, const char * function,
			  word line, const char * msg, va_list va);

void debug(DebugLevel level, const char * filename, const char * function,
		   word line, const char * msg, ...);

#ifdef C4_DEBUG

#ifdef __GNUC__
__attribute__((noreturn))
#endif
void fail(const char * filename, const char * function, word line, const char * msg, ...);

#define FAIL(...) fail(__FILE__, __FUNCTION__, __LINE__, __VA_ARGS__)

#define LOG(...) debug(DEBUG_LOG, __FILE__, __FUNCTION__, __LINE__, __VA_ARGS__)

#define ASSERT(cond) (cond ? (void)0 : FAIL("assertion failed : " #cond))
#else

#define FAIL(...) __builtin_unreachable()
#define LOG(...) (void)0
#define ASSERT(cond) ((cond) ? (void)0 : __builtin_unreachable())
#endif

void dump_tokens(Str src);
