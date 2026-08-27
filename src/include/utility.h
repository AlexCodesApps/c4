#pragma once
#include "assert.h"
#include "checked_math.h"
#include "debug.h" // IWYU pragma: keep
#include "fmt.h"   // IWYU pragma: keep
#include "ints.h"
#include "platform.h"
#include <signal.h>
#include <stdarg.h>
#include <stdlib.h>

NORETURN
static inline void crash(void) {
	fflush(stderr);
	fflush(stdout);
	raise(SIGABRT);
	_Exit(127); // fallback
}

#ifdef C4_DEBUG
#define TODO(...) FAIL("TODO REACHED: " __VA_ARGS__)
#define UNREACHABLE() FAIL("THE UNREACHABLE WAS REACHED...")
#else
#define TODO(...) FAIL_RELEASE("This code path is unimplemented...")
#define UNREACHABLE() COMPILER_UNREACHABLE()
#endif

#define ZERO(ptr) memset(ptr, 0, sizeof(*(ptr)))

typedef enum {
	DONT_REPORT_ERROR = 0,
	DO_REPORT_ERROR = 1,
} ReportError;

NODISCARD static inline bool align_usize(usize integer, usize alignment,
										 usize * out) {
	usize mask = alignment - 1;
	usize result;
	if (UNLIKELY(!ckd_add_usize(integer, mask, &result))) {
		return false;
	}
	*out = result & ~mask;
	return true;
}

NODISCARD static inline bool align_ptr(void * ptr, usize alignment,
									   void ** out) {
	usize mask = alignment - 1;
	usize result;
	if (UNLIKELY(!ckd_add_usize((usize)ptr, mask, &result))) {
		return false;
	}
	*out = (void *)(result & ~mask);
	return true;
}

NODISCARD static inline word bit_width_usize(usize u) {
#ifdef __GNUC__
	if (u == 0)
		return 0;
	return USIZE_MAX_BITWIDTH - (word)__builtin_clzll(u);
#else
	word accum = 0;
	while (u) {
		u >>= 1;
		++accum;
	}
	return accum;
#endif
}

NODISCARD static inline word leading_zeros_usize(usize u) {
#ifdef __GNUC__
	if (u == 0)
		return USIZE_MAX_BITWIDTH;
	return (word)__builtin_clzll(u);
#else
	u = ~u;
	word accum = 0;
	while (u & ((usize)1 << (USIZE_MAX_BITWIDTH - 1))) {
		u <<= 1;
		++accum;
	}
	return accum;
#endif
}

NODISCARD static inline bool is_0_or_pow2_usize(usize u) {
	return !(u & (u - 1));
}

NODISCARD static inline usize next_pow2_usize(usize u) {
	if (is_0_or_pow2_usize(u))
		return u;
	return (usize)1 << bit_width_usize(u);
}

STD_PRINTF_FN(3, 4)
// temporary stop gap bc the uscases are hacky
// and probably better suited for custom
// temporary arena backed formatting
NODISCARD static inline bool snprintf_bool(char * buf, size_t bufsz,
										   const char * fmt, ...) {
	va_list va;
	va_start(va, fmt);
	int result = vsnprintf(buf, bufsz, fmt, va);
	va_end(va);
	return 0 <= result && (unsigned)result < bufsz;
}

#define KB(n) ((n) * 1024)
#define MB(n) ((n) * 1024 * 1024)
#define GB(n) ((u64)(n) * 1024 * 1024 * 1024)
