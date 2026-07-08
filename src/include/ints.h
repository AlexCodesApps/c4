#pragma once
#include <stdbool.h>
#include <stdint.h>
typedef uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;
typedef uintptr_t usize;
typedef int8_t i8;
typedef int16_t i16;
typedef int32_t i32;
typedef int64_t i64;
typedef intptr_t isize;
typedef float f32;
typedef double f64;
typedef i32 iword;
typedef u32 word;

#define USIZE_MAX ((usize) - 1)
#define ISIZE_MAX ((isize)(USIZE_MAX >> 1))
#define USIZE_MAX_BITWIDTH (sizeof(usize) * 8)
#define U64_MAX ((u64) - 1)
