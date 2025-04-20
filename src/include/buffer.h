#pragma once

#include "ints.h"
#include "str.h"
#include "utility.h"
#include "writer.h"
#include <assert.h>

struct Buffer {
    u8 * data;
    usize size;
} typedef Buffer;

struct BufferedWriter {
    Writer writer;
    Buffer buffer;
    usize cursor;
} typedef BufferedWriter;

BufferedWriter buffered_writer_new(Writer writer, Buffer buffer);
bool buffered_write(BufferedWriter buffer[ref], const u8 *, usize size);
bool buffered_flush(BufferedWriter buffer[ref]);
Writer buffered_writer_writer(BufferedWriter buffer[ref]);

static Buffer buffer_new(u8 * data, usize size) {
    return (Buffer){ data, size };
}

static u8 * buffer_at(Buffer buffer, usize index) {
    assert(index < buffer.size);
    return buffer.data + index;
}

static u8 buffer_at_value_s(Buffer buffer, usize index) {
    if (index >= buffer.size) {
        return '\0';
    }
    return buffer.data[index];
}

static Str buffer_as_str(Buffer buffer) {
    return str_new((const char *)buffer.data, buffer.size);
}

#define foreach_buffer(addr, iter) \
for (u8 * iter = (addr)->data, * _end_ = iter + (addr)->size; \
    iter != _end_; \
    ++iter)

#define b(array) buffer_new((array), sizeof(array))
