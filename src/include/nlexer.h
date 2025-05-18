#pragma once
#include "common.h"
#include "tokens.h"

struct NLexer {
    Str src;
    SrcPos pos;
} typedef NLexer;

struct NLexerError {
    SrcPos pos;
    char unexpected_char;
} typedef NLexerError;

struct NLexerTokenResult {
    bool ok;
    union {
        Token token;
        NLexerError error;
    } as;
} typedef NLexerTokenResult;

NLexer nlexer_new(Str src);
NLexerTokenResult nlexer_next(NLexer lexer[ref]);
usize nlexer_index(const NLexer lexer[ref]);
bool nlexer_eof(const NLexer lexer[ref]);
