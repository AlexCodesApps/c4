#include "include/writer.h"
#include "include/buffer.h"
#include "include/file.h"
#include "include/str.h"
#include <stdio.h>

static WriterResult
file_write_(WriterPayload payload, const void * data, usize size) {
    File file = {payload.udata};
    return file_write(file, data, size);
}

static WriterResult
cfile_write(WriterPayload payload, const void * data, usize size) {
    FILE * file = payload.pdata;
    int r = fwrite(data, 1, size, file);
    return r == size;
}

static WriterResult cfile_flush(WriterPayload payload) {
    FILE * file = payload.pdata;
    return fflush(file) == 0;
}

static WriterResult
str_builder_write(WriterPayload payload, const void * data, usize size) {
    StrBuilder * str = payload.pdata;
    return str_builder_append(str, str_new(data, size));
}

Writer file_writer(File file) {
    return (Writer){.write = file_write_,
                    .flush = noop_writer_flush,
                    .payload.udata = file.fd};
}

Writer cfile_writer(FILE file[ref]) {
    return (Writer){
        .write = cfile_write,
        .flush = cfile_flush,
        .payload.pdata = file,
    };
}

Writer str_builder_writer(StrBuilder str[ref]) {
    return (Writer){
        .write = str_builder_write,
        .flush = noop_writer_flush,
        .payload.pdata = str,
    };
}

WriterResult writer_write(Writer writer, const void * data, usize size) {
    return writer.write(writer.payload, data, size);
}

WriterResult writer_byte(Writer writer, u8 c) {
    return writer.write(writer.payload, &c, 1);
}

WriterResult writer_str(Writer writer, Str str) {
    return writer.write(writer.payload, str.data, str.size);
}

void writer_flush(Writer writer) { writer.flush(writer.payload); }

Writer stderr_writer() { return file_writer(stderr_file()); }

// TODO: make thread_safe!
Writer stdout_writer() {
    static u8 buffer[4096];
    static BufferedWriter buffered_writer = {
        .buffer.data = nullptr,
    };
    if (buffered_writer.buffer.data == nullptr) {
        Writer base_file_writer = file_writer(stdout_file());
        buffered_writer = buffered_writer_new(base_file_writer, b(buffer));
    }
    return buffered_writer_writer(&buffered_writer);
}
