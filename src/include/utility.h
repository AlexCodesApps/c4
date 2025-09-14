#pragma once
#include "assert.h"
#include "checked_math.h"
#include "ints.h"
#include <memory.h>
#include <stdbool.h>
#include <stdio.h> // IWYU pragma: keep

#define BREAKPOINT()                                                           \
	asm("int3\n"                                                               \
		"nop\n") // not portable but program is borked anyways
#define ZERO(ptr) memset(ptr, 0, sizeof(*(ptr)))
#define UNREACHABLE() assert(false && "unreachable")
#define TODO(...)                                                              \
	do {                                                                       \
		__VA_OPT__(fputs("REACHED TODO: " __VA_ARGS__ "\n", stderr));          \
		assert(false && "todo");                                               \
	} while (0)
#ifdef __GNUC__
#define UNLIKELY(...) __builtin_expect(!!(__VA_ARGS__), 0)
#define LIKELY(...) __builtin_expect(!!(__VA_ARGS__), 1)
#define FALLTHROUGH() __attribute__((fallthrough))
#else
#define UNLIKELY(...) (__VA_ARGS__)
#define LIKELY(...) (__VA_ARGS__)
#define FALLTHROUGH()
#endif

typedef enum {
	DONT_REPORT_ERROR = 0,
	DO_REPORT_ERROR = 1,
} ReportError;

static inline bool align_usize(usize integer, usize alignment, usize * out) {
	usize mask = alignment - 1;
	usize result;
	if (UNLIKELY(!ckd_add_usize(integer, mask, &result))) {
		return false;
	}
	*out = result & ~mask;
	return true;
}

static inline bool align_ptr(void * ptr, usize alignment, void ** out) {
	usize mask = alignment - 1;
	usize result;
	if (UNLIKELY(!ckd_add_usize((usize)ptr, mask, &result))) {
		return false;
	}
	*out = (void *)(result & ~mask);
	return true;
}

static inline word bit_width_usize(usize u) {
	word accum = 0;
	while (u) {
		u >>= 1;
		++accum;
	}
	return accum;
}

static inline word leading_zeros_usize(usize u) {
	u = ~u;
	word accum = 0;
	while (u & ((usize)1 << (sizeof(u) * 8 - 1))) {
		u <<= 1;
		++accum;
	}
	return accum;
}

#define KB(n) ((n) * 1024)
#define MB(n) ((n) * 1024 * 1024)
#define GB(n) ((n) * 1024 * 1024 * 1024)
