#pragma once

#include "common.h"
#include "ints.h"

typedef struct SemaFn SemaFn;
typedef struct SemaDecl SemaDecl;
typedef struct SemaEnv SemaEnv;
typedef struct SemaCtx SemaCtx;
typedef struct SemaValue SemaValue;

typedef usize SymbolID;

typedef enum {
	IR_INST_RET,
	IR_INST_I32,
	IR_INST_I64,
	IR_INST_FN,
	IR_INST_VAR,
	IR_INST_LOAD_I32,
	IR_INST_LOAD_I64,
	IR_INST_ADD_I32,
	IR_INST_CALL,
	IR_INST_POP,
} IrInstType;

typedef struct {
	IrInstType type;
	i32 i32;
} IrInstI32;

typedef struct {
	u8 * code;
	usize count;
	usize capacity;
} IrFn;

bool emit_fn(SemaCtx * ctx, VisitorState visitor, SemaFn * fn);
bool run_implemented_const_fn(SemaCtx * ctx, SemaFn * fn, SemaValue * out); // the dream
