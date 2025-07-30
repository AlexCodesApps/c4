#pragma once
#include "ints.h" // IWYU pragma: keep

#define ckd_add(a, b, c) (!__builtin_add_overflow((a), (b), (c)))
#define ckd_sub(a, b, c) (!__builtin_sub_overflow((a), (b), (c)))
#define ckd_mul(a, b, c) (!__builtin_mul_overflow((a), (b), (c)))
#define ckd_div(a, b, c) (((b) != 0) ? (*(c) = (a) / (b), true) : false)
#define ckd_add_ptr(a, b, c) ckd_add((usize)(a), (b), (usize *)(c))
#define ckd_sub_ptr(a, b, c) ckd_sub((usize)(a), (b), (usize *)(c))
