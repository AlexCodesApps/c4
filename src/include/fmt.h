#pragma once
#include "i128.h"
#include <stdio.h>

void c4print(FILE * file, const char * msg);
void c4println(FILE * file, const char * msg);
void c4print_decimal(FILE * file, bool sign, I128 i);
// | FORMAT   | USAGE                              |
// |----------|------------------------------------|
// | %uw      | print integer u* <= u32            |
// | %uq      | print integer u64                  |
// | %udq     | print integer u128                 |
// | %iw      | print integer u* <= i32            |
// | %iq      | print integer i64                  |
// | %s       | print Str                          |
// | %cs      | print const char *                 |
// | %ch      | print ascii code of integer <= *32 |
// | %%       | print '%'                          |
// | %ti      | print TokenIndex                   |
void c4printf(FILE * file, const char * path, ...);
void c4vaprintf(FILE * file, const char * path, va_list va);
