#include <memory.h>
#include "include/str.h"

bool str_equal(Str a, Str b) {
	if (a.size != b.size) {
		return false;
	}
	return memcmp(a.data, b.data, a.size) == 0;
}

bool str_copy(VMemArena * arena, Str str, Str * out) {
	char * buffer = vmem_arena_alloc_bytes(arena, str.size, alignof(char));
	if (!buffer) {
		return false;
	}
	memcpy(buffer, str.data, str.size);
	*out = str_new(buffer, str.size);
	return true;
}
