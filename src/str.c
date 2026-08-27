#include "include/str.h"
#include <string.h>

bool str_equal(Str a, Str b) {
	if (a.size != b.size) {
		return false;
	}
	if (a.size == 0) {
		return true; // avoid UB
	}
	return memcmp(a.data, b.data, a.size) == 0;
}

bool str_copy(VMemArena * arena, Str str, Str * out) {
	if (str.size == 0) {
		*out = str_new(NULL, 0);
		return true;
	}
	char * buffer = vmem_arena_alloc_bytes(arena, str.size, 1);
	if (!buffer) {
		return false;
	}
	memcpy(buffer, str.data, str.size);
	*out = str_new(buffer, str.size);
	return true;
}

void str_split_at_idx(Str str, usize idx, Str * pre, Str * post) {
	if (str.size <= idx) {
		*pre = str;
		*post = s("");
		return;
	}
	*pre = str_new(str.data, idx);
	*post = str_new(str.data + idx, str.size - idx);
}

Str str_get_line_at_idx(Str str, isize idx) {
	isize begin;
	for (begin = idx - 1; 0 <= begin; --begin)
		if (str.data[begin] == '\n')
			break;
	begin += 1;
	isize end;
	for (end = idx; end < (isize)str.size; ++end)
		if (str.data[end] == '\n')
			break;
	const char * ptr = str.data + begin;
	usize size = (usize)(end - begin);
	return str_new(ptr, size);
}

static void str_line_iter_align_line_start(StrLineIter * iter) {
	isize begin;
	for (begin = iter->idx - 1; 0 <= begin; --begin)
		if (iter->src.data[begin] == '\n')
			break;
	iter->idx = begin + 1;
}

void str_line_iter_new(StrLineIter * iter, Str str, isize idx) {
	iter->src = str;
	iter->idx = idx;
	str_line_iter_align_line_start(iter);
}

Str str_line_iter_current_line(StrLineIter * iter) {
	isize end;
	for (end = iter->idx; end < (isize)iter->src.size; ++end)
		if (iter->src.data[end] == '\n')
			break;
	usize size = (usize)(end - iter->idx);
	return str_new(iter->src.data + iter->idx, size);
}

bool str_line_iter_last_line(StrLineIter * iter, Str * out) {
	isize end = iter->idx - 1;
	if (end < 0)
		return false;
	isize begin;
	for (begin = end - 1; 0 <= begin; --begin)
		if (iter->src.data[begin] == '\n')
			break;
	begin += 1;
	iter->idx = begin;
	usize size = (usize)(end - begin);
	*out = str_new(iter->src.data + begin, size);
	return true;
}

bool str_line_iter_next_line(StrLineIter * iter, Str * out) {
	isize begin;
	for (begin = iter->idx + 1; begin < (isize)iter->src.size; ++begin) {
		if (iter->src.data[begin] == '\n') {
			begin += 1;
			break;
		}
	}
	if (begin > (isize)iter->src.size)
		return false;
	iter->idx = begin;
	*out = str_line_iter_current_line(iter);
	return true;
}
