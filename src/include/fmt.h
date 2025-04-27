#pragma once
#include "list_macros.h"
#include "macros.h"
#include "str.h"
#include "utility.h"
#include "writer.h"
#include <string.h>

static bool fmt_str(Writer writer, Str fmt, Str str) {
    return writer_str(writer, str);
}
static bool fmt_cstr(Writer writer, Str fmt, const char * data) {
    return writer_write(writer, data, strlen(data));
}

static bool fmt_char(Writer writer, Str fmt, char c) {
    return writer_byte(writer, c);
}

bool fmt_u64(Writer writer, Str fmt, u64 i);
bool fmt_u32(Writer writer, Str fmt, u32 i);
bool fmt_u16(Writer writer, Str fmt, u16 i);
bool fmt_u8(Writer writer, Str fmt, u8 i);

bool fmt_i64(Writer writer, Str fmt, i64 i);
bool fmt_i32(Writer writer, Str fmt, i32 i);
bool fmt_i16(Writer writer, Str fmt, i16 i);
bool fmt_i8(Writer writer, Str fmt, i8 i);

bool fmt_f64(Writer writer, Str fmt, f64 f);
bool fmt_f32(Writer writer, Str fmt, f32 f);

bool fmt_ptr(Writer writer, Str fmt, const void * ptr);

bool fmt_str_builder(Writer writer, Str fmt, const StrBuilder builder[ref]);

#define fmt_generic_apply(writer, fmt, arg)                                    \
    _Generic((arg),                                                            \
        Str: fmt_str,                                                          \
        char *: fmt_cstr,                                                      \
        const char *: fmt_cstr,                                                \
        char: fmt_char,                                                        \
        u64: fmt_u64,                                                          \
        u32: fmt_u32,                                                          \
        u16: fmt_u16,                                                          \
        u8: fmt_u8,                                                            \
        i64: fmt_i64,                                                          \
        i32: fmt_i32,                                                          \
        i16: fmt_i16,                                                          \
        i8: fmt_i8,                                                            \
        f64: fmt_f64,                                                          \
        f32: fmt_f32,                                                          \
        void *: fmt_ptr,                                                       \
        const void *: fmt_ptr,                                                 \
        StrBuilder *: fmt_str_builder,                                         \
        const StrBuilder *: fmt_str_builder)(writer, fmt, arg)
#define _DETAIL_FMT_BEGIN_(arg)                                                \
    if ((MACRO_VAR(status) = fmt_helper(MACRO_VAR(writer), &MACRO_VAR(slice),  \
                                        &MACRO_VAR(fmt_str))) == 0) {          \
        if (!fmt_generic_apply(MACRO_VAR(writer), MACRO_VAR(fmt_str), arg)) {  \
            MACRO_VAR(status) = -1;                                            \
        }
#define _DETAIL_FMT_END_(...) }
#define fmt(_writer, str, ...)                                                 \
    ({                                                                         \
        Writer MACRO_VAR(writer) = _writer;                                    \
        int MACRO_VAR(status) = 0;                                             \
        bool MACRO_VAR(return);                                                \
        Str MACRO_VAR(slice) = s(str);                                         \
        Str MACRO_VAR(fmt_str);                                                \
        FOREACH_RECURSE_MACRO(_DETAIL_FMT_BEGIN_, _DETAIL_FMT_END_,            \
                              __VA_ARGS__);                                    \
        if (MACRO_VAR(status) == 1 || MACRO_VAR(status) == 0) {                \
            MACRO_VAR(status) = fmt_helper(                                    \
                MACRO_VAR(writer), &MACRO_VAR(slice), &MACRO_VAR(fmt_str));    \
        }                                                                      \
        MACRO_VAR(return) = MACRO_VAR(status) == 1;                            \
        MACRO_VAR(return);                                                     \
    })

int fmt_helper(Writer writer, Str slice[ref], Str fmt_slice[ref]);
