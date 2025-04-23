#pragma once
#include "../allocator.h" // IWYU pragma: keep
#include "../macros.h"

#define DARRAY_UPPER_NAME(upper_name, lower_name, type) upper_name
#define DARRAY_LOWER_NAME(upper_name, lower_name, type) lower_name
#define DARRAY_TYPE(upper_name, lower_name, type) type

#define DARRAY_HEADER(template)                                                \
    struct template(DARRAY_UPPER_NAME) {                                       \
        template(DARRAY_TYPE) * data;                                          \
        usize size;                                                            \
        usize capacity;                                                        \
        Allocator allocator;                                                   \
    }                                                                          \
    typedef template(DARRAY_UPPER_NAME);                                       \
    template(DARRAY_UPPER_NAME)                                                \
        CONCAT(template(DARRAY_LOWER_NAME), _new)(Allocator allocator);        \
    bool CONCAT(template(DARRAY_LOWER_NAME), _push)(                           \
        template(DARRAY_UPPER_NAME) array[ref], template(DARRAY_TYPE) value    \
    );                                                                         \
    void CONCAT(template(DARRAY_LOWER_NAME), _free)(template(DARRAY_UPPER_NAME \
    ) array[ref]);
#define DARRAY_IMPL(template)                                                  \
    template(DARRAY_UPPER_NAME)                                                \
        CONCAT(template(DARRAY_LOWER_NAME), _new)(Allocator allocator) {       \
        return (template(DARRAY_UPPER_NAME)                                    \
        ){.data = nullptr, .size = 0, .capacity = 0, .allocator = allocator};  \
    }                                                                          \
    bool CONCAT(template(DARRAY_LOWER_NAME), _push)(                           \
        template(DARRAY_UPPER_NAME) array[ref], template(DARRAY_TYPE) value    \
    ) {                                                                        \
        if (array->size >= array->capacity) {                                  \
            usize new_capacity = (array->size + 1) * 2;                        \
            template(DARRAY_TYPE) * new_alloc = allocator_alloc_n(             \
                array->allocator, template(DARRAY_TYPE), new_capacity          \
            );                                                                 \
            if (!new_alloc) {                                                  \
                return false;                                                  \
            }                                                                  \
            memcpy(                                                            \
                new_alloc, array->data, array->size * sizeof(*array->data)     \
            );                                                                 \
            array->data = new_alloc;                                           \
            array->capacity = new_capacity;                                    \
        }                                                                      \
        array->data[array->size++] = value;                                    \
        return true;                                                           \
    }                                                                          \
    void CONCAT(template(DARRAY_LOWER_NAME), _free)(template(DARRAY_UPPER_NAME \
    ) array[ref]) {                                                            \
        allocator_deallocate(array->allocator, array->data);                   \
    }
