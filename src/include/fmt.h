#pragma once
#include <stdio.h>

void c4print(FILE * file, const char * msg);
void c4println(FILE * file, const char * msg);
// | FORMAT   | USAGE                              |
// |----------|------------------------------------|
// | %uw      | print integer u* <= u32            |
// | %uq      | print integer u64                  |
// | %iw      | print integer u* <= i32            |
// | %iq      | print integer i64                  |
// | %s       | print Str                          |
// | %cs      | print const char *                 |
// | %ch      | print ascii code of integer <= *32 |
// | %%       | print '%'                          |
// | %ti      | print TokenIndex                   |
void c4printf(FILE * file, const char * path, ...);
void c4vaprintf(FILE * file, const char * path, va_list va);
