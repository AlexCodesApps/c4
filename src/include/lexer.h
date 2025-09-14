#pragma once
#include "ints.h"
#include "str.h"

typedef enum {
	TOKEN_LPAREN,
	TOKEN_RPAREN,
	TOKEN_LBRACE,
	TOKEN_RBRACE,
	TOKEN_COLON,
	TOKEN_SEMICOLON,
	TOKEN_PLUS,
	TOKEN_COMMA,
	TOKEN_EQ,
	TOKEN_STAR,
	TOKEN_AMPERSAND,

	TOKEN_CONST,
	TOKEN_FN,
	TOKEN_LET,
	TOKEN_MUT,
	TOKEN_NULLPTR,
	TOKEN_RETURN,
	TOKEN_TYPE_,
	TOKEN_VOID,

	TOKEN_IDEN,
	TOKEN_INT,

	TOKEN_EOF,
	TOKEN_ERR,
} TokenKind;
#define TOKEN_COUNT TOKEN_ERR

typedef u32 TokenIndex;
#define TOKEN_INDEX_MAX UINT32_MAX

typedef struct {
	TokenKind kind;
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
Str lexer_token_str(const Lexer * lexer, const Token * token);
usize lexer_row(const Lexer * lexer);
usize lexer_col(const Lexer * lexer);
bool lexer_eof(const Lexer * lexer);
