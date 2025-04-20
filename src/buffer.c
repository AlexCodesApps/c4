#include "include/buffer.h"
#include "include/writer.h"
#include <string.h>

BufferedWriter buffered_writer_new(Writer writer, Buffer buffer) {
    return (BufferedWriter) {
        .writer = writer,
        .buffer = buffer,
        .cursor = 0,
    };
}

bool buffered_write(BufferedWriter buffer[ref], const u8 * data, usize size) {
    if (size > buffer->buffer.size) {
        if (!buffered_flush(buffer)) {
            return false;
        }
        return writer_write(buffer->writer, data, size);
    }
    const usize mem_left = buffer->buffer.size - buffer->cursor;
    if (size > mem_left) {
        if (!buffered_flush(buffer)) {
            return false;
        }
    }
    memcpy(buffer->buffer.data + buffer->cursor, data, size);
    buffer->cursor += size;
    return true;
}

bool buffered_flush(BufferedWriter buffer[ref]) {
    if (!writer_write(buffer->writer, buffer->buffer.data, buffer->cursor)) {
        return false;
    }
    writer_flush(buffer->writer);
    buffer->cursor = 0;
    return true;
}

WriterResult buffered_writer_write_(WriterPayload payload, const void * data, usize size) {
    BufferedWriter * writer = payload.pdata;
    return buffered_write(writer, data, size);
}

WriterResult buffered_writer_flush_(WriterPayload payload) {
    BufferedWriter * writer = payload.pdata;
    return buffered_flush(writer);
}

Writer buffered_writer_writer(BufferedWriter buffer[ref]) {
    return (Writer) {
        .write = buffered_writer_write_,
        .flush = buffered_writer_flush_,
        .payload.pdata = buffer,
    };
}
