#pragma once
#include "ints.h"
#include "utility.h"

static inline word get_segmented_slot(usize size) {
	return bit_width_usize(size + 1) - 1;
}

static inline usize get_segmented_slot_index(usize size, word slot) {
	return size - ((usize)1 << slot) + 1;
}
