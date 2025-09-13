#pragma once
#include "ast.h"

typedef enum {
	PARSE_RESULT_OK,
	PARSE_RESULT_OOM,
	PARSE_RESULT_OVERFLOW,
	PARSE_RESULT_ERROR,
} ParseResult;

ParseResult parse_src(VMemArena * arena, Str path, Str src, Ast * out);
