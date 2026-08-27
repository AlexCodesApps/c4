#pragma once
#include "arena.h"
#include "ints.h"
#include <string.h>

typedef struct {
	const char * data;
	usize size;
} Str;

#define s(lit) ((Str){(lit), sizeof(lit) - 1})

static inline Str str_new(const char * data, usize size) {
	return (Str){.data = data, .size = size};
}

static inline Str str_from_cstr(const char * cstr) {
	return str_new(cstr, strlen(cstr));
}

static inline bool str_empty(Str str) { return str.size == 0; }

bool str_equal(Str a, Str b);
bool str_copy(VMemArena * arena, Str str, Str * out);
Str str_get_line_at_idx(Str str, isize idx);
void str_split_at_idx(Str str, usize idx, Str * pre, Str * post);

typedef struct {
	Str src;
	isize idx;
} StrLineIter;

void str_line_iter_new(StrLineIter * iter, Str str, isize idx);
Str str_line_iter_current_line(StrLineIter * iter);
bool str_line_iter_last_line(StrLineIter * iter, Str * out);
bool str_line_iter_next_line(StrLineIter * iter, Str * out);
