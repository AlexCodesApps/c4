#pragma once
#include "ints.h"
#include "checked_math.h"
#include "assert.h"
#include <stdbool.h>
#include <memory.h>

#define BREAKPOINT() asm("int3\n""nop\n") // not portable but program is borked anyways
#define ZERO(ptr) memset(ptr, 0, sizeof(*ptr))
#define UNREACHABLE() assert(false && "unreachable")
#ifdef __GNUC__
#define UNLIKELY(...) __builtin_expect(!!(__VA_ARGS__), 0)
#define LIKELY(...) __builtin_expect(!!(__VA_ARGS__), 1)
#else
#define UNLIKELY(...) (__VA_ARGS__)
#define LIKELY(...) (__VA_ARGS__)
#endif

typedef enum {
	DONT_REPORT_ERROR = 0,
	DO_REPORT_ERROR = 1,
} ReportError;

static inline bool align_usize(usize integer, usize alignment, usize * out) {
    usize mask = alignment - 1;
    usize result;
    if (UNLIKELY(!ckd_add(integer, mask, &result))) {
        return false;
    }
    *out = result & ~mask;
    return true;
}

static inline bool align_ptr(void * ptr, usize alignment, void ** out) {
    usize mask = alignment - 1;
    usize result;
    if (UNLIKELY(!ckd_add((usize)ptr, mask, &result))) {
        return false;
    }
    *out = (void *)(result & ~mask);
    return true;
}

#define KB(n) ((n) * 1024)
#define MB(n) ((n) * 1024 * 1024)
#define GB(n) ((n) * 1024 * 1024 * 1024)

// shield your eyes
#ifdef __clang__
#define PRIVATE [[deprecated("private")]]
#define PRIVATE_IMPL_BEGIN \
	_Pragma("clang diagnostic push") \
	_Pragma("clang diagnostic ignored \"-Wdeprecated-declarations\"")
#define PRIVATE_IMPL_END \
	_Pragma("clang diagnostic pop")
#elif defined(__GNUC__)
#define PRIVATE [[deprecated("private")]]
#define PRIVATE_IMPL_BEGIN \
	_Pragma("GCC diagnostic push") \
	_Pragma("GCC diagnostic ignored \"-Wdeprecated-declarations\"")
#define PRIVATE_IMPL_END \
	_Pragma("GCC diagnostic pop")
#else
#define PRIVATE
#define PRIVATE_IMPL_BEGIN
#define PRIVATE_IMPL_END
#endif
