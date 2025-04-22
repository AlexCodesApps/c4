#pragma once
#define EXPAND(...) EXPAND4(EXPAND4(EXPAND4(EXPAND4(__VA_ARGS__))))
#define EXPAND4(...) EXPAND3(EXPAND3(EXPAND3(EXPAND3(__VA_ARGS__))))
#define EXPAND3(...) EXPAND2(EXPAND2(EXPAND2(EXPAND2(__VA_ARGS__))))
#define EXPAND2(...) EXPAND1(EXPAND1(EXPAND1(EXPAND1(__VA_ARGS__))))
#define EXPAND1(...) __VA_ARGS__
#define PARENS ()
#define FOREACH_MACRO_H(macro, a, ...)                                         \
    macro(a) __VA_OPT__(FOREACH_MACRO_A PARENS(macro, __VA_ARGS__))
#define FOREACH_MACRO_A() FOREACH_MACRO_H
#define FOREACH_MACRO(macro, ...)                                              \
    __VA_OPT__(EXPAND(FOREACH_MACRO_H(macro, __VA_ARGS__)))
#define MAP_MACRO_H(macro, a, ...)                                             \
    macro(a) __VA_OPT__(, MAP_MACRO_A PARENS(macro, __VA_ARGS__))
#define MAP_MACRO(macro, ...) EXPAND(MAP_MACRO_H(macro, __VA_ARGS__))
#define MAP_MACRO_A() MAP_MACRO_H
#define LIST_SIZE_MACRO(...) EXPAND(LIST_SIZE_MACRO_H(__VA_ARGS__))
#define LIST_SIZE_MACRO_H(x, ...)                                              \
    (1 __VA_OPT__(+LIST_SIZE_MACRO_A PARENS(__VA_ARGS__)))
#define LIST_SIZE_MACRO_A() LIST_SIZE_MACRO_H
#define FOREACH_RECURSE_MACRO_H(begin, end, a, ...)                            \
    begin(a)                                                                   \
        __VA_OPT__(FOREACH_RECURSE_MACRO_A PARENS(begin, end, __VA_ARGS__))    \
            end(a)
#define FOREACH_RECURSE_MACRO_A() FOREACH_RECURSE_MACRO_H
#define FOREACH_RECURSE_MACRO(begin, end, ...)                                 \
    __VA_OPT__(EXPAND(FOREACH_RECURSE_MACRO_H(begin, end, __VA_ARGS__)))
