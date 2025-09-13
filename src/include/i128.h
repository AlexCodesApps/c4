#pragma once

#include "ints.h"

typedef struct {
	u64 low;
	u64 high;
} I128;

I128 i128_new(u64 high, u64 low);
