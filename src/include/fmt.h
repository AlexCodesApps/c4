#pragma once
#include "ints.h"
#include "str.h"
#include <stdio.h>

// | FORMAT   | USAGE                              |
// |----------|------------------------------------|
// | %uw      | print integer u* <= u32            |
// | %uq      | print integer u64                  |
// | %iw      | print integer u* <= i32            |
// | %iq      | print integer i64                  |
// | %idq     | print integer i128                 |
// | %s print | Str                                |
// | %cs      | print const char *                 |
// | %ch      | print ascii code of integer <= *32 |
// | %%       | print '%'                          |
// | %ti      | print TokenIndex                   |
void c4printf(FILE * file, const char * path, ...);
void c4vaprintf(FILE * file, const char * path, va_list va);
