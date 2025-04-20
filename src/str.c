#include "include/str.h"
#include "include/allocator.h"
#include "include/checked_math.h"
#include "include/utility.h"
#include <string.h>

StrBuilder str_builder_new(Allocator allocator) {
    return (StrBuilder) {
        .allocator = allocator,
        .data = nullptr,
        .size = 0,
        .capacity = 0,
    };
}

void str_builder_clear(StrBuilder str[ref]) {
    str_builder_free(str);
    str->data = nullptr;
    str->size = 0;
    str->capacity = 0;
}
void str_builder_free(StrBuilder str[ref]) {
    allocator_deallocate(str->allocator, str->data);
}

bool str_builder_append(StrBuilder str[ref], Str src) {
    if (src.size == 0) {
        return true;
    }
    usize new_size = src.size + str->size;
    if (new_size > str->capacity) {
        usize new_capacity = (str->capacity + src.size) * 2;
        void * alloc = allocator_alloc_uninit_n(str->allocator, u8, new_capacity);
        if (!alloc) {
            return false;
        }
        memcpy(alloc, str->data, str->size);
        allocator_deallocate(str->allocator, str->data);
        str->capacity = new_capacity;
        str->data = alloc;
    }
    memcpy(str->data + str->size, src.data, src.size);
    str->data[new_size] = '\0';
    str->size = new_size;
    return true;
}

bool str_builder_push(StrBuilder str[ref], char c) {
    if (str->size == str->capacity) {
        usize new_capacity = (str->capacity + 1) * 2;
        void * alloc = allocator_alloc_uninit_n(str->allocator, u8, new_capacity);
        if (!alloc) {
            return false;
        }
        memcpy(alloc, str->data, str->size);
        allocator_deallocate(str->allocator, str->data);
        str->capacity = new_capacity;
        str->data = alloc;
    }
    str->data[str->size++] = c;
    str->data[str->size] = '\0';
    return true;
}

Str str_builder_slice(const StrBuilder str[ref]) {
    return (Str) {
        .data = str->data,
        .size = str->size,
    };
}

const char * str_builder_cstr(const StrBuilder str[ref]) {
    return str->data;
}

bool str_eq(Str a, Str b) {
    if (a.size != b.size) {
        return false;
    }
    return memcmp(a.data, b.data, a.size) == 0;
}

bool str_empty(Str a) {
    return a.size == 0;
}

bool str_starts_with(Str str, Str prefix) {
    if (str.size < prefix.size) return false;
    return memcmp(str.data, prefix.data, prefix.size) == 0;
}

Str str_slice_start(Str str, usize size) {
    return (Str){ .data = str.data, .size = MIN(str.size, size) };
}

Str str_slice_end(Str str, usize start) {
    usize size;
    if (!ckd_sub(str.size, start, &size)) {
        size = 0;
    }
    return (Str) {
        .data = str.data + start,
        .size = size,
    };
}

Str str_slice(Str str, usize start, usize count) {
    if (start > str.size) {
        return EMPTY_STR;
    }
    usize size;
    if (!ckd_sub(str.size, start, &size)) {
        return EMPTY_STR;
    }
    size = MIN(size, count);
    return (Str) {
        .data = str.data + start,
        .size = size,
    };
}

Str str_slice_iter(Str str, usize start, usize end) {
    if (end < start || start > str.size) {
        return EMPTY_STR;
    }
    usize size = MIN(end - start, str.size - start);
    return (Str) {
        .data = str.data + start,
        .size = size,
    };
}

bool str_split_char(Str src, Str begin[ref], Str end[ref], char c) {
    for (usize i = 0; i < src.size; ++i) {
        if (*str_at(&src, i) == c) {
            *begin = str_slice_start(src, i);
            *end = str_slice_end(src, i + 1);
            return true;
        }
    }
    return false;
}

isize str_find_char(Str str, char c) {
    for (usize i  = 0; i < str.size; ++i) {
        if (str_at_value_s(str, i) == c) {
            return i;
        }
    }
    return NPOS;
}
