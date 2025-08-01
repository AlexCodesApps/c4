#pragma once
#include "ints.h"
#include "str.h"

typedef enum : u32 {
	TOKEN_LPAREN,
	TOKEN_RPAREN,
	TOKEN_LBRACE,
	TOKEN_RBRACE,
	TOKEN_COLON,
	TOKEN_SEMICOLON,
	TOKEN_PLUS,
	TOKEN_COMMA,
	TOKEN_EQ,

	TOKEN_FN,
	TOKEN_LET,
	TOKEN_MUT,
	TOKEN_RETURN,
	TOKEN_TYPE,
	TOKEN_VOID,

	TOKEN_IDEN,
	TOKEN_INT,

	TOKEN_EOF,
	TOKEN_ERR,
} TokenType;

typedef u32 TokenIndex;
#define TOKEN_INDEX_MAX UINT32_MAX

typedef struct {
	TokenType type;
	TokenIndex start;
	TokenIndex end;
} Token;

typedef struct {
	Str src;
	usize index;
	u32 row;
	u32 col;
} Lexer;

Lexer lexer_new(Str src);
Token lexer_next(Lexer * lexer);
Str   lexer_token_str(const Lexer * lexer, const Token * token);
usize lexer_row(const Lexer * lexer);
usize lexer_col(const Lexer * lexer);
bool  lexer_eof(const Lexer * lexer);
