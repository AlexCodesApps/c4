#pragma once
#include "allocator.h"
#include "ints.h"
#include <assert.h>
#include <string.h> // IWYU pragma: keep

struct Str {
    const char * data;
    usize size;
} typedef Str;

#define s(input) ((struct Str){(input), sizeof(input) - 1})
#define cstr(input) ((struct Str){(input), strlen(input)})

struct StrBuilder {
    Allocator allocator;
    char * data;
    usize size;
    usize capacity;
} typedef StrBuilder;

StrBuilder str_builder_new(Allocator allocator);
void str_builder_clear(StrBuilder str[ref]);
void str_builder_free(StrBuilder str[ref]);
bool str_builder_append(StrBuilder str[ref], Str src);
bool str_builder_push(StrBuilder str[ref], char c);
Str str_builder_slice(const StrBuilder str[ref]);
const char * str_builder_cstr(const StrBuilder str[ref]);

bool str_eq(Str a, Str b);
bool str_empty(Str a);
bool str_starts_with(Str str, Str prefix);

Str str_slice_start(Str str, usize size);
Str str_slice_end(Str str, usize size);
Str str_slice(Str str, usize start, usize count);
Str str_slice_iter(Str str, usize start, usize end);

bool str_split_char(Str src, Str str[ref], Str out[ref], char c);

#define NPOS -1;
isize str_find_char(Str str, char c);

static const char * str_at(Str src[ref], usize index) {
    assert(index < src->size);
    return &src->data[index];
}

static char str_at_value_s(Str src, usize index) {
    if (index >= src.size) {
        return '\0';
    }
    return src.data[index];
}

static Str str_new(const char * data, usize size) { return (Str){data, size}; }

#define EMPTY_STR (Str){0, 0};
