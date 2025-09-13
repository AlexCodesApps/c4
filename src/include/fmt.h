#pragma once

#include "ints.h"
#include "str.h"

typedef bool (*FmtWriteFn)(void * ctx, const void * data, usize size);
typedef bool (*FmtFlushFn)(void * ctx);

typedef struct {
	FmtWriteFn writefn;
	FmtFlushFn flushfn;
} FmtVTable;

typedef struct {
	const FmtVTable * vtable;
	union {
		void * p_ctx;
		usize u_ctx;
	};
} FmtWriter;

bool fmt_write(FmtWriter writer, const void * data, usize size);
bool fmt_byte(FmtWriter writer, u8 b);
bool fmt_cstr(FmtWriter writer, const char * str);
bool fmt_str(FmtWriter writer, Str str);
bool fmt_int(FmtWriter writer, Str fmt, isize i);
bool fmt_uint(FmtWriter writer, Str fmt, usize u);
