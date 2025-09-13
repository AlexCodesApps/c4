#include "include/i128.h"

I128 i128_new(u64 high, u64 low) {
	return (I128){
		.low = low,
		.high = high,
	};
}

bool i128_mul_u64(I128 i, u64 u, I128 * out) {}
