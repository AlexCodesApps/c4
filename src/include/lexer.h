#pragma once
#include "allocator.h"
#include "common.h"
#include "generic/darray.h"
#include "str.h"
#include <setjmp.h>

enum TokenType {
    TOKEN_TYPE_SEMICOLON,
    TOKEN_TYPE_LPAREN,
    TOKEN_TYPE_RPAREN,
    TOKEN_TYPE_COMMA,
    TOKEN_TYPE_SCOPE,
    TOKEN_TYPE_COLON,
    TOKEN_TYPE_LBRACE,
    TOKEN_TYPE_RBRACE,
    TOKEN_TYPE_DOT,
    TOKEN_TYPE_DOTSTAR,
    TOKEN_TYPE_STAR,
    TOKEN_TYPE_PLUS,
    TOKEN_TYPE_MINUS,
    TOKEN_TYPE_EQ,
    TOKEN_TYPE_AMPERSAND,

    TOKEN_TYPE_FN,
    TOKEN_TYPE_AS,
    TOKEN_TYPE_LET,
    TOKEN_TYPE_CONST,
    TOKEN_TYPE_RETURN,
    TOKEN_TYPE_MOD,
    TOKEN_TYPE_PUB,
    TOKEN_TYPE_STRUCT,

    TOKEN_TYPE_IDENTIFIER,
    TOKEN_TYPE_INTEGER,

    TOKEN_TYPE_EOF,
} typedef TokenType;

static Str token_type_to_str(TokenType type) {
    switch (type) {
    case TOKEN_TYPE_SEMICOLON:
        return s("TOKEN_TYPE_SEMICOLON");
    case TOKEN_TYPE_LPAREN:
        return s("TOKEN_TYPE_LPAREN");
    case TOKEN_TYPE_RPAREN:
        return s("TOKEN_TYPE_RPAREN");
    case TOKEN_TYPE_COMMA:
        return s("TOKEN_TYPE_COMMA");
    case TOKEN_TYPE_SCOPE:
        return s("TOKEN_TYPE_SCOPE");
    case TOKEN_TYPE_COLON:
        return s("TOKEN_TYPE_COLON");
    case TOKEN_TYPE_LBRACE:
        return s("TOKEN_TYPE_LBRACE");
    case TOKEN_TYPE_RBRACE:
        return s("TOKEN_TYPE_RBRACE");
    case TOKEN_TYPE_DOT:
        return s("TOKEN_TYPE_DOT");
    case TOKEN_TYPE_DOTSTAR:
        return s("TOKEN_TYPE_DOTSTAR");
    case TOKEN_TYPE_STAR:
        return s("TOKEN_TYPE_STAR");
    case TOKEN_TYPE_PLUS:
        return s("TOKEN_TYPE_PLUS");
    case TOKEN_TYPE_MINUS:
        return s("TOKEN_TYPE_MINUS");
    case TOKEN_TYPE_EQ:
        return s("TOKEN_TYPE_EQ");
    case TOKEN_TYPE_AMPERSAND:
        return s("TOKEN_TYPE_AMPERSAND");

    case TOKEN_TYPE_FN:
        return s("TOKEN_TYPE_FN");
    case TOKEN_TYPE_AS:
        return s("TOKEN_TYPE_AS");
    case TOKEN_TYPE_LET:
        return s("TOKEN_TYPE_LET");
    case TOKEN_TYPE_CONST:
        return s("TOKEN_TYPE_CONST");
    case TOKEN_TYPE_RETURN:
        return s("TOKEN_TYPE_RETURN");
    case TOKEN_TYPE_MOD:
        return s("TOKEN_TYPE_MOD");
    case TOKEN_TYPE_PUB:
        return s("TOKEN_TYPE_PUB");
    case TOKEN_TYPE_STRUCT:
        return s("TOKEN_TYPE_STRUCT");

    case TOKEN_TYPE_IDENTIFIER:
        return s("TOKEN_TYPE_IDENTIFIER");
    case TOKEN_TYPE_INTEGER:
        return s("TOKEN_TYPE_INTEGER");

    case TOKEN_TYPE_EOF:
        return s("TOKEN_TYPE_EOF");
    }
}

struct Token {
    SrcSpan span;
    TokenType type;
} typedef Token;

enum LexErrorType {
    LEX_ERROR_OOM,
    LEX_ERROR_UNEXPECTED_CHAR,
} typedef LexErrorType;

struct LexError {
    LexErrorType type;
    char unexpected_char;
    SrcPos pos;
} typedef LexError;

#define TOKEN_LIST_TEMPLATE(m) m(TokenList, token_list, Token)
DARRAY_HEADER(TOKEN_LIST_TEMPLATE);

struct TokenSpan {
    Token * data;
    usize size;
} typedef TokenSpan;

static TokenSpan token_list_to_span(TokenList list[ref]) {
    return (TokenSpan){.data = list->data, .size = list->size};
}

struct LexResult {
    bool succeeded;
    union {
        struct {
            TokenList list;
        };
        LexError err;
    };
} typedef LexResult;

struct Lexer {
    Str src;
    SrcPos pos;
    LexError err;
    jmp_buf catch_site;
    TokenList tokens;
} typedef Lexer;

LexResult lex(Allocator allocator, Str src);
bool validate_ascii(Str src);
Str token_get_str(Token token, Str src);
