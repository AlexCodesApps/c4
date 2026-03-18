#pragma once
#include "ints.h"
#include "platform.h"

typedef struct {
	u64 low;
	u64 high;
} I128;

NODISCARD I128 i128_new(u64 high, u64 low);
NODISCARD bool i128_add_u64(I128 a, u64 u, I128 * out);
NODISCARD bool i128_add(I128 a, I128 b, I128 * out);
NODISCARD I128 i128_add_wrapping(I128 a, I128 b);
NODISCARD bool i128_sub(I128 a, I128 b, I128 * out);
NODISCARD I128 i128_sub_wrapping(I128 a, I128 b);
NODISCARD bool i128_mul_by_10(I128 * inout);
u64 i128_div_by_10(I128 * inout);
