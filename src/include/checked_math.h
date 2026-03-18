#pragma once
#include "ints.h" // IWYU pragma: keep

static inline bool ckd_add_usize(usize a, usize b, usize * c) {
	if (USIZE_MAX - a < b) {
		return false;
	}
	*c = a + b;
	return true;
}

static inline bool ckd_sub_usize(usize a, usize b, usize * c) {
	if (b > a) {
		return false;
	}
	*c = a - b;
	return true;
}

#define ckd_add_u64 ckd_add_usize
#define ckd_sub_u64 ckd_sub_usize

static inline bool ckd_add_ptr(void * a, usize b, void ** c) {
	return ckd_add_usize((usize)a, b, (usize *)c);
}

static inline bool ckd_mul_usize(usize a, usize b, usize * c) {
	if (USIZE_MAX / a < b) {
		return false;
	}
	*c = a * b;
	return true;
}
