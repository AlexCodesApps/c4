#include "include/fmt.h"
#include "include/checked_math.h"
#include "include/file.h"
#include "include/str.h"
#include "include/writer.h"
#include <stdio.h>

bool fmt_u64(Writer writer, Str fmt, u64 u) {
    usize pow = 1;
    for (usize i = u; i >= 10; i /= 10) {
        if (!ckd_mul(pow, 10, &pow)) {
            writer_str(writer, s("<integer too large>"));
            return false;
        }
    }
    for (usize i = pow; i > 0; i /= 10) {
        u8 digit = (u / i) % 10;
        if (!writer_byte(writer, digit + '0')) {
            return false;
        }
    }
    return true;
}

bool fmt_i64(Writer writer, Str fmt, i64 i) {
    if (i < 0) {
        if (!writer_byte(writer, '-')) {
            return false;
        }
        i = -i;
    }
    return fmt_u64(writer, fmt, i);
}

bool fmt_u32(Writer writer, Str fmt, u32 i) { return fmt_u64(writer, fmt, i); }
bool fmt_u16(Writer writer, Str fmt, u16 i) { return fmt_u64(writer, fmt, i); }
bool fmt_u8(Writer writer, Str fmt, u8 i) { return fmt_u64(writer, fmt, i); }

bool fmt_i32(Writer writer, Str fmt, i32 i) { return fmt_i64(writer, fmt, i); }
bool fmt_i16(Writer writer, Str fmt, i16 i) { return fmt_i64(writer, fmt, i); }
bool fmt_i8(Writer writer, Str fmt, i8 i) { return fmt_i64(writer, fmt, i); }

bool fmt_f64(Writer writer, Str fmt, f64 f) {
    char buff[64];
    int len = snprintf(buff, sizeof(buff), "%lf", f);
    if (len < 0) {
        return false;
    }
    return writer_write(writer, buff, len);
}

bool fmt_f32(Writer writer, Str fmt, f32 f) { return fmt_f64(writer, fmt, f); }

bool fmt_ptr(Writer writer, Str fmt, const void * ptr) {
    char buff[64];
    int len = snprintf(buff, sizeof(buff), "%p", ptr);
    if (len < 0) {
        return false;
    }
    return writer_write(writer, buff, len);
}

bool fmt_str_builder(Writer writer, Str fmt, const StrBuilder builder[ref]) {
    return fmt(writer, "StrBuilder({})", str_builder_slice(builder));
}

int fmt_helper(Writer writer, Str slice[ref], Str fmt_slice[ref]) {
    Str writer_failed = s("\n<fmt parse error: writer failed>\n");
    Writer stderrw = cfile_writer(stderr);
    Str str = *slice;
    for (usize index = 0; index < str.size; ++index) {
        char c = *str_at(&str, index);
        if (c == '}') {
            if (str_at_value_s(str, index + 1) != '}') {
                writer_str(stderrw, s("\n<fmt parse error: expected '}'>\n"));
                return -1;
            }
            if (!writer_byte(writer, '}')) {
                writer_str(stderrw, writer_failed);
                return -2;
            }
            ++index;
            continue;
        }
        if (c != '{') {
            if (!writer_byte(writer, c)) {
                writer_str(stderrw, writer_failed);
                return -2;
            }
            continue;
        }
        if (str_at_value_s(str, index + 1) == '{') {
            if (!writer_byte(writer, '{')) {
                writer_str(stderrw, writer_failed);
                return -2;
            }
            ++index;
            continue;
        }
        for (usize index2 = index + 1; index2 < str.size; ++index2) {
            char c = *str_at(&str, index2);
            if (c == '{') {
                writer_str(stderrw, s("\n<fmt parse error: unexpected '{'>\n"));
                return -1;
            }
            if (c != '}') {
                continue;
            }
            *fmt_slice = str_slice_iter(str, index + 1, index2);
            *slice = str_slice_end(str, index2 + 1);
            return 0;
        }
        writer_str(stderrw, s("\n<fmt parse error: unterminated '{'>\n"));
        return -1;
    }
    return 1;
}
