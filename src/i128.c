#include "include/i128.h"
#include "include/checked_math.h"
#include <stdbit.h>

I128 i128_new(u64 high, u64 low) {
	return (I128){
		.low = low,
		.high = high,
	};
}

bool i128_add_u64(I128 a, u64 u, I128 * out) {
	word carry = (u64)(-1) - a.low < u;
	a.low += u;
	if (!ckd_add(a.high, carry, &a.high)) {
		return false;
	}
	*out = a;
	return true;
}

bool i128_add(I128 a, I128 b, I128 * out) {
	word carry = (u64)(-1) - a.low < b.low;
	a.low += b.low;
	if (!ckd_add(a.high, b.high, &a.high)) {
		return false;
	}
	if (!ckd_add(a.high, carry, &a.high)) {
		return false;
	}
	*out = a;
	return true;
}

I128 i128_add_wrapping(I128 a, I128 b) {
	word carry = (u64)(-1) - a.low < b.low;
	a.low += b.low;
	a.high += b.high + carry;
	return a;
}

bool i128_shift_left(I128 i, word shift, I128 * out) {
	word offset;
	if (i.high) {
		offset = stdc_leading_zeros(i.high);
	} else {
		offset = sizeof(i.high) * 8 + stdc_leading_zeros(i.low);
	}
	if (offset < shift) {
		return false;
	}
	i.high <<= shift;
	u64 mask = (1U << shift) - 1;
	word mask_offset = sizeof(mask) * 8 - shift;
	mask <<= mask_offset;
	i.high |= (i.low & mask) >> mask_offset;
	i.low <<= mask;
	*out = i;
	return true;
}

bool i128_mul_by_10(I128 * out) {
	word offset = stdc_leading_zeros(out->high);
	if (offset < 3) {
		return false;
	}
	I128 a, b;
	a.high = out->high << 3;
	a.high |= (out->low & 0xE000000000000000) >> 61;
	a.low = out->low << 3;
	b.high = out->high << 1;
	b.high |= (out->low & 0x8000000000000000) >> 63;
	b.low = out->low << 1;
	word carry = (u64)(-1) - a.low < b.low;
	a.low += b.low;
	a.high += b.high + carry;
	*out = a;
	return true;
}
