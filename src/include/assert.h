#pragma once
#include "file.h" // IWYU pragma: keep
#include "fmt.h"
#include "macros.h"
#include <stdlib.h> // IWYU pragma: keep

#define ASSERT_FAILED_WITH_MSG(str, msg, ...)                                  \
    (fmt(stderr_writer(),                                                      \
         "{}:{}:{}: assertion failed: (" str ") with msg: " msg "\n",          \
         __FILE__, __LINE__, __PRETTY_FUNCTION__ __VA_OPT__(, __VA_ARGS__)))
#define ASSERT_FAILED(str, ...)                                                \
    (fmt(stderr_writer(), "{}:{}:{}: assertion failed: " str "\n", __FILE__,   \
         __LINE__, __PRETTY_FUNCTION__ __VA_OPT__(, __VA_ARGS__)))
#ifndef NDEBUG
#define ASSERT(b, ...)                                                         \
    ((b) ? (void)(0)                                                           \
         : (FST(__VA_OPT__(ASSERT_FAILED_WITH_MSG, )                           \
                    ASSERT_FAILED)(#b __VA_OPT__(, __VA_ARGS__)),              \
            abort()))
#else
#define ASSERT(b, ...) ((void)(0))
#endif
#define TODO (ASSERT(false, "todo reached!"))
