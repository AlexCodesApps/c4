#pragma once
#include "ast.h"
#include "lexer.h"

typedef enum {
	PARSE_RESULT_OK,
	PARSE_RESULT_OOM,
	PARSE_RESULT_OVERFLOW,
	PARSE_RESULT_ERROR,
} ParseResult;

ParseResult parse_src(VMemArena * arena, Str src, Ast * out);
