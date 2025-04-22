#pragma once
#include "ints.h"
#include "str.h"

typedef bool WriterResult;

union WriterPayload {
    void * pdata;
    usize udata;
} typedef WriterPayload;

typedef WriterResult (*WriterWriteCallback)(WriterPayload, const void * data,
                                            usize size);
typedef WriterResult (*WriterFlushCallback)(WriterPayload);

struct Writer {
    WriterWriteCallback write;
    WriterFlushCallback flush;
    WriterPayload payload;
} typedef Writer;

Writer str_builder_writer(StrBuilder builder[ref]);

WriterResult writer_write(Writer writer, const void * data, usize size);
WriterResult writer_byte(Writer writer, u8 c);
WriterResult writer_str(Writer writer, Str str);
void writer_flush(Writer writer);

static WriterResult noop_writer_flush(WriterPayload _) { return true; }
