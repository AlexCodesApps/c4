#include "include/i128.h"
#include "include/checked_math.h"
#include "include/utility.h"

I128 i128_new(u64 high, u64 low) {
	return (I128){
		.low = low,
		.high = high,
	};
}

bool i128_add_u64(I128 a, u64 u, I128 * out) {
	word carry = U64_MAX - a.low < u;
	a.low += u;
	if (!ckd_add_u64(a.high, carry, &a.high)) {
		return false;
	}
	*out = a;
	return true;
}

bool i128_add(I128 a, I128 b, I128 * out) {
	word carry = U64_MAX - a.low < b.low;
	a.low += b.low;
	if (!ckd_add_u64(a.high, b.high, &a.high)) {
		return false;
	}
	if (!ckd_add_u64(a.high, carry, &a.high)) {
		return false;
	}
	*out = a;
	return true;
}

I128 i128_add_wrapping(I128 a, I128 b) {
	word carry = U64_MAX - a.low < b.low;
	a.low += b.low;
	a.high += b.high + carry;
	return a;
}

bool i128_sub(I128 a, I128 b, I128 * out) {
	word carry = b.low > a.low;
	a.low -= b.low;
	if (!ckd_sub_u64(a.high, b.high, &a.high)) {
		return false;
	}
	if (!ckd_sub_u64(a.high, carry, &a.high)) {
		return false;
	}
	*out = a;
	return true;
}

I128 i128_sub_wrapping(I128 a, I128 b) {
	word carry = b.low > a.low;
	a.low -= b.low;
	a.high -= b.high + carry;
	return a;
}

bool i128_shift_left(I128 i, word shift, I128 * out) {
	word offset;
	if (i.high) {
		offset = leading_zeros_usize(i.high);
	} else {
		offset = sizeof(i.high) * 8 + leading_zeros_usize(i.low);
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

bool i128_mul_by_10(I128 * inout) {
	if (inout->high > 0x1999999999999999 && inout->low > 0x9999999999999999) {
		return false;
	}
	I128 a, b;
	a.high = inout->high << 3;
	a.high |= (inout->low & 0xE000000000000000) >> 61;
	a.low = inout->low << 3;
	b.high = inout->high << 1;
	b.high |= (inout->low & 0x8000000000000000) >> 63;
	b.low = inout->low << 1;
	word carry = U64_MAX - a.low < b.low;
	a.low += b.low;
	a.high += b.high + carry;
	*inout = a;
	return true;
}

word bit_width_i128(I128 value) {
	if (value.high == 0) {
		return bit_width_usize(value.low);
	}
	return bit_width_usize(value.high) + USIZE_MAX_BITWIDTH;
}

bool i128_gte(I128 a, I128 b) {
	if (a.high > b.high)
		return true;
	if (a.high < b.high)
		return false;
	return a.low >= b.low;
}

u64 i128_div_by_10(I128 * inout) {
	const I128 _10 = i128_new(0, 10);
	I128 remainder = *inout;
	I128 quot = i128_new(0, 0);
	word bitw = bit_width_i128(remainder);
	for (iword i = (iword)bitw - 1; i >= 0; --i) {
		I128 mult;
		if (UNLIKELY(!i128_shift_left(_10, (word)i, &mult))) {
			continue;
		}
		if (i128_sub(remainder, mult, &remainder)) {
			I128 part = i128_new(0, 1);
			ASSERT(i128_shift_left(part, (word)i, &part));
			quot = i128_add_wrapping(quot, part);
		}
	}
	ASSERT(remainder.high == 0);
	return remainder.low;
}
