#pragma once

#include "ints.h"

typedef struct {
	u64 low;
	u64 high;
} I128;

I128 i128_new(u64 high, u64 low);
bool i128_add_u64(I128 a, u64 u, I128 * out);
bool i128_add(I128 a, I128 b, I128 * out);
I128 i128_add_wrapping(I128 a, I128 b);
bool i128_mul_by_10(I128 * out);
