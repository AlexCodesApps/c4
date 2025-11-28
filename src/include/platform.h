#pragma once

#ifdef __GNUC__
#define NORETURN __attribute__((noreturn))
#define STD_PRINTF_FN(fmt_idx, varargs_idx) \
	__attribute__((__format__(__printf__, fmt_idx, varargs_idx)))
#define UNLIKELY(...) __builtin_expect(!!(__VA_ARGS__), 0)
#define LIKELY(...) __builtin_expect(!!(__VA_ARGS__), 1)
#define FALLTHROUGH() __attribute__((fallthrough))
#define COMPILER_UNREACHABLE() __builtin_unreachable()
#else
#define NORETURN
#define STD_PRINTF_FN(fmt_idx, varargs_idx)
#define UNLIKELY(...) (__VA_ARGS__)
#define LIKELY(...) (__VA_ARGS__)
#define FALLTHROUGH() (void)0
#define COMPILER_UNREACHABLE() (void)0
#endif
