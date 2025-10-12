#include "include/str.h"
#include <memory.h>

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
	char * buffer = vmem_arena_alloc_bytes(arena, str.size, _Alignof(char));
	if (!buffer) {
		return false;
	}
	memcpy(buffer, str.data, str.size);
	*out = str_new(buffer, str.size);
	return true;
}
