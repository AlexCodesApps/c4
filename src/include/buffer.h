#pragma once

#include "ints.h"

typedef struct {
	u8 * data;
	usize size;
} Buffer;

static inline Buffer buffer_new(u8 * data, usize size) {
	Buffer buffer;
	buffer.data = data;
	buffer.size = size;
	return buffer;
}

#define b(a) ((Buffer){ (a), sizeof(a) })
