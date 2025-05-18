#pragma once

#include "generic/darray.h"
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

static SrcSpan src_span_new(SrcPos pos, usize len) {
    return (SrcSpan){
        .pos = pos,
        .len = len,
    };
}

static Str src_span_slice(SrcSpan span, Str str) {
    return str_slice(str, span.pos.index, span.len);
}

#define STR_LIST_TEMPLATE(m) m(StrList, str_list, Str)
DARRAY_HEADER(STR_LIST_TEMPLATE);

struct StrSpan {
    const Str * data;
    usize size;
} typedef StrSpan;

static StrSpan str_list_to_span(const StrList list[ref]) {
    return (StrSpan){
        .data = list->data,
        .size = list->size,
    };
}

struct Path {
    SrcSpan span;
    bool is_global;
    StrSpan list;
} typedef Path;

struct PathBuilder {
    SrcSpan span;
    bool is_global;
    StrList list;
} typedef PathBuilder;

static Path path_builder_to_path(const PathBuilder builder[ref]) {
    return (Path){
        .span = builder->span,
        .is_global = builder->is_global,
        .list = str_list_to_span(&builder->list),
    };
}
