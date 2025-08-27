#pragma once
#include "arena.h"
#include "ints.h"
#include <string.h>

typedef struct {
	const char * data;
	usize size;
} Str;

#define s(lit) ((Str){ (lit), sizeof(lit) - 1 })

static inline Str str_new(const char * data, usize size) {
	return (Str){ .data = data, .size = size };
}

static inline Str str_from_cstr(const char * cstr) {
	return str_new(cstr, strlen(cstr));
}

static inline bool str_empty(Str str) {
	return str.size == 0;
}

bool str_equal(Str a, Str b);
bool str_copy(VMemArena * arena, Str str, Str * out);
