#pragma once
#include "i128.h"
#include "str.h"
#include <stdio.h>

#define TABWIDTH 4

void c4print(FILE * file, const char * msg);
void c4println(FILE * file, const char * msg);
void c4print_decimal(FILE * file, bool sign, I128 i);
// | FORMAT | USAGE                              |
// |--------|------------------------------------|
// | %uw    | print integer u* <= u32            |
// | %uq    | print integer u64                  |
// | %udq   | print integer u128                 |
// | %iw    | print integer u* <= i32            |
// | %iq    | print integer i64                  |
// | %s     | print Str                          |
// | %cs    | print const char *                 |
// | %ch    | print ascii code of integer <= *32 |
// | %%     | print '%'                          |
// | %ti    | print TokenIndex                   |
// | %ts    | print TypeSig                      |
// | %th    | print TypeHandle                   |
void c4printf(FILE * file, const char * path, ...);
void c4vaprintf(FILE * file, const char * path, va_list va);

usize c4cellwidth(Str str);
void c4usr_print(FILE * file, Str str);
void c4print_errline(FILE * file, usize count);
void c4print_space(FILE * file, usize count);

typedef enum {
	C4FMT_COLOR_RED,
} C4FmtColor;

void c4setcolor(FILE * file, C4FmtColor color);
void c4resetcolor(FILE * file);
