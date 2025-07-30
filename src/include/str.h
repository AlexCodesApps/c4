#pragma once
#include "arena.h"
#include "ints.h"

typedef struct {
	const char * data;
	usize size;
} Str;

#define s(lit) ((Str){ (lit), sizeof(lit) - 1 })

static inline Str str_new(const char * data, usize size) {
	return (Str){ .data = data, .size = size };
}

bool str_equal(Str a, Str b);
bool str_copy(VMemArena * arena, Str str, Str * out);
