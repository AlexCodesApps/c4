#include "include/lexer.h"
#include "include/allocator.h"
#include "include/common.h"
#include "include/generic/darray.h"
#include "include/ints.h"
#include "include/str.h"
#include "include/utility.h"
#include "include/fmt.h"
#include <setjmp.h>
#include <ctype.h>

struct _str_ttype_pair {
    Str str;
    TokenType ttype;
};

static const struct _str_ttype_pair keywords[] = {
    {s("fn"), TOKEN_TYPE_FN},
    {s("as"), TOKEN_TYPE_AS},
    {s("let"), TOKEN_TYPE_LET},
    {s("const"), TOKEN_TYPE_CONST},
    {s("return"), TOKEN_TYPE_RETURN},
    {s("mod"), TOKEN_TYPE_MOD},
    {s("pub"), TOKEN_TYPE_PUB},
};

static const struct _str_ttype_pair operators[] = {
    {s(";"), TOKEN_TYPE_SEMICOLON},
    {s(".*"), TOKEN_TYPE_DOTSTAR},
    {s("("), TOKEN_TYPE_LPAREN},
    {s(")"), TOKEN_TYPE_RPAREN},
    {s(","), TOKEN_TYPE_COMMA},
    {s("::"), TOKEN_TYPE_SCOPE},
    {s(":"), TOKEN_TYPE_COLON},
    {s("{"), TOKEN_TYPE_LBRACE},
    {s("}"), TOKEN_TYPE_RBRACE},
    {s("."), TOKEN_TYPE_DOT},
    {s("*"), TOKEN_TYPE_STAR},
    {s("+"), TOKEN_TYPE_PLUS},
    {s("-"), TOKEN_TYPE_MINUS},
    {s("="), TOKEN_TYPE_EQ},
    {s("&"), TOKEN_TYPE_AMPERSAND},
};

[[noreturn]]static void throw(Lexer lexer[ref], LexError error) {
    lexer->err = error;
    longjmp(lexer->catch_site, 1);
}

static bool lex_eof(Lexer * lexer) {
    return lexer->pos.index >= lexer->src.size;
}

static char peek(Lexer * lexer) {
    if (lex_eof(lexer)) {
        return '\0';
    }
    return lexer->src.data[lexer->pos.index];
}

static bool advance(Lexer * lexer) {
    char c = peek(lexer);
    if (c == '\0') {
        return false;
    }
    if (c == '\n') {
        lexer->pos.col = 1;
        ++lexer->pos.row;
    } else {
        ++lexer->pos.col;
    }
    ++lexer->pos.index;
    return true;
}

static void advance_by(Lexer * lexer, usize offset) {
    while (offset--) {
        if (!advance(lexer)) {
            return;
        }
    }
}

static char peek_advance(Lexer * lexer) {
    char c = peek(lexer);
    advance(lexer);
    return c;
}

static SrcPos lexer_get_pos(Lexer * lexer) {
    return lexer->pos;
}

static void lexer_push_token(Lexer * lexer, Token tok) {
    if (!token_list_push(&lexer->tokens, tok)) {
        throw(lexer, (LexError) {
            .type = LEX_ERROR_OOM,
        });
    }
}

static bool lexer_get_iden(Lexer * lexer, Str * iden) {
    SrcPos pos = lexer_get_pos(lexer);
    usize start = pos.index;
    char c = peek(lexer);
    if (c != '_' && !isalpha(c)) {
        return false;
    }
    advance(lexer);
    usize size = 1;
    while ((c = peek(lexer)) == '_' || isalnum(c)) {
        advance(lexer);
        ++size;
    }
    *iden = str_slice(lexer->src, start, size);
    return true;
}

static bool lexer_get_number(Lexer * lexer, SrcSpan * span) {
    SrcPos pos = lexer_get_pos(lexer);
    usize start = pos.index;
    char c = peek(lexer);
    if (!isdigit(c)) {
        return false;
    }
    advance(lexer);
    usize size = 1;
    while (isalnum(c = peek(lexer))) {
        if (isalpha(c)) {
            throw(lexer, (LexError) {
                .type = LEX_ERROR_UNEXPECTED_CHAR,
                .unexpected_char = c,
                .pos = lexer_get_pos(lexer),
            });
        }
        advance(lexer);
        ++size;
    }
    *span = (SrcSpan) {
        .pos = pos,
        .len = size,
    };
    return true;
}

static void lex_main(Lexer * lexer) {
    char c;
    while ((c = peek(lexer)) != '\0') {
        if (c != ' ' && c != '\n' && c != '\t' && c != '\r') {
            break;
        }
        advance(lexer);
        continue;
    }
    if (c == '\0') {
        return;
    }
    Str operator_slice = str_slice_end(lexer->src, lexer_get_pos(lexer).index);
    for (usize i = 0; i < ARRAY_SIZE(operators); ++i) {
        const struct _str_ttype_pair * pair = operators + i;
        if (str_starts_with(operator_slice, pair->str)) {
            SrcPos pos = lexer_get_pos(lexer);
            advance_by(lexer, pair->str.size);
            TokenType ttype = pair->ttype;
            Token tok = (Token) {
                .span = {
                    .pos = pos,
                    .len = pair->str.size,
                },
                .type = ttype,
            };
            lexer_push_token(lexer, tok);
            return;
        }
    }
    SrcPos pos = lexer_get_pos(lexer);
    Str iden;
    if (lexer_get_iden(lexer, &iden)) {
        for (usize i = 0; i < ARRAY_SIZE(keywords); ++i) {
            const struct _str_ttype_pair * pair = keywords + i;
            if (str_eq(iden, pair->str)) {
                TokenType ttype = pair->ttype;
                Token tok = (Token) {
                    .span = {
                        .pos = pos,
                        .len = iden.size,
                    },
                    .type = ttype,
                };
                lexer_push_token(lexer, tok);
                return;
            }
        }
        Token tok = (Token) {
            .span = {
                .pos = pos,
                .len = iden.size,
            },
            .type = TOKEN_TYPE_IDENTIFIER,
        };
        lexer_push_token(lexer, tok);
        return;
    }
    SrcSpan span;
    if (lexer_get_number(lexer, &span)) {
        Token tok = (Token) {
            .span = span,
            .type = TOKEN_TYPE_INTEGER,
        };
        lexer_push_token(lexer, tok);
        return;
    }
    throw(lexer, (LexError) {
        .type = LEX_ERROR_UNEXPECTED_CHAR,
        .unexpected_char = peek(lexer),
        .pos = lexer_get_pos(lexer),
    });
}

LexResult lex(Allocator allocator, Str src) {
    jmp_buf buff;
    Lexer lexer;
    if (setjmp(buff) != 0) {
        token_list_free(&lexer.tokens);
        return (LexResult){
            .succeeded = false,
            .err = lexer.err,
        };
    }
    lexer = (Lexer) {
        .src = src,
        .pos = {
            .row = 1,
            .col = 1,
            .index = 0,
        },
        .catch_site = *buff,
        .tokens = token_list_new(allocator),
    };
    while (!lex_eof(&lexer)) {
        lex_main(&lexer);
    }
    lexer_push_token(&lexer, (Token) {
        .type = TOKEN_TYPE_EOF,
        .span = (SrcSpan) {
            .pos = lexer_get_pos(&lexer),
            .len = 0,
        }
    });
    return (LexResult) {
        .succeeded = true,
        .list = lexer.tokens,
    };
}

bool validate_ascii(Str src) {
    foreach_span(&src, i) {
        char c = *i;
        if (c < 1 || c > 127) {
            return false;
        }
    }
    return true;
}

Str token_get_str(Token token, Str src) {
    return str_slice(src, token.span.pos.index, token.span.len);
}

DARRAY_IMPL(TOKEN_LIST_TEMPLATE);
