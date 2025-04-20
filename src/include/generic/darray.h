#pragma once
#include "../macros.h"
#include "../allocator.h" // IWYU pragma: keep

#define T_UPPER_NAME(upper_name, lower_name, type) upper_name
#define T_LOWER_NAME(upper_name, lower_name, type) lower_name
#define T_TYPE(upper_name, lower_name, type) type

#define DARRAY_HEADER(template) \
struct template(T_UPPER_NAME) { \
    template(T_TYPE) * data; \
    usize size; \
    usize capacity; \
    Allocator allocator; \
} typedef template(T_UPPER_NAME); \
template(T_UPPER_NAME) CONCAT(template(T_LOWER_NAME), _new)(Allocator allocator); \
bool CONCAT(template(T_LOWER_NAME), _push)(template(T_UPPER_NAME) array[ref], template(T_TYPE) value); \
void CONCAT(template(T_LOWER_NAME), _free)(template(T_UPPER_NAME) array[ref]);
#define DARRAY_IMPL(template) \
template(T_UPPER_NAME) CONCAT(template(T_LOWER_NAME), _new)(Allocator allocator) { \
    return (template(T_UPPER_NAME)) { \
        .data = nullptr, \
        .size = 0, \
        .capacity = 0, \
        .allocator = allocator \
    };   \
} \
bool CONCAT(template(T_LOWER_NAME), _push)(template(T_UPPER_NAME) array[ref], template(T_TYPE) value) { \
    if (array->size >= array->capacity) { \
        usize new_capacity = (array->size + 1) * 2; \
        template(T_TYPE) * new_alloc = allocator_alloc_n(array->allocator, template(T_TYPE), new_capacity); \
        if (!new_alloc) { \
            return false; \
        } \
        memcpy(new_alloc, array->data, array->size * sizeof(*array->data)); \
        array->data = new_alloc; \
        array->capacity = new_capacity; \
    } \
    array->data[array->size++] = value; \
    return true; \
} \
void CONCAT(template(T_LOWER_NAME), _free)(template(T_UPPER_NAME) array[ref]) { \
    allocator_deallocate(array->allocator, array->data); \
}
