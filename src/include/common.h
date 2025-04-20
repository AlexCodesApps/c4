#pragma once

#include "ints.h"
#include "str.h"

struct SrcPos {
    usize index;
    usize row;
    usize col;
} typedef SrcPos;

struct SrcSpan {
    SrcPos pos;
    usize len;
} typedef SrcSpan;

static Str src_span_slice(SrcSpan span, Str str) {
    return str_slice(str, span.pos.index, span.len);
}
