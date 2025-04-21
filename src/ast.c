#include "include/ast.h"
#include "include/allocator.h"
#include "include/common.h"
#include "include/file.h"
#include "include/generic/darray.h"
#include "include/lexer.h"
#include "include/str.h"
#include "include/writer.h"
#include "include/fmt.h"
#include <setjmp.h>

static void recover_nested(Parser * parser);
static bool parse_tls(Parser * parser, AstTopLvlStmt * out);
static bool parse_function(Parser * parser, AstDecl * out);
static bool parse_decl(Parser * parser, AstDecl * out);
static bool parse_stmt_block(Parser * parser, AstStmtList * out);
static bool parse_function_param(Parser * parser, AstFunParam * out);
static void parse_function_param_list_recover_invalid_param(Parser * parser);
static void parse_function_recover_invalid_return_type(Parser * parser);
static bool parse_function_param_list(Parser * parser, AstFunParamList * out);
static AstType parse_type(Parser * parser);
static AstExpr parse_expr(Parser * parser);

static SrcSpan extend_span_to(SrcPos begin, const Parser * parser) {
    return (SrcSpan) {
        .pos = begin,
        .len = parser->index - begin.index,
    };
}

static bool expr_is_ok(AstExpr * expr) {
    return expr->type != AST_EXPR_POISONED;
}
static bool type_is_ok(AstType * type) {
    return type->type != AST_TYPE_POISONED;
}

DARRAY_IMPL(AST_TYPE_LIST_TEMPLATE);
DARRAY_IMPL(AST_TOP_LVL_STMT_LIST_TEMPLATE);
DARRAY_IMPL(AST_ERROR_LIST_TEMPLATE);
DARRAY_IMPL(AST_FUN_PARAM_LIST_TEMPLATE);
DARRAY_IMPL(AST_STMT_LIST_TEMPLATE);
DARRAY_IMPL(AST_EXPR_LIST_TEMPLATE);
DARRAY_IMPL(STR_LIST_TEMPLATE);

[[noreturn]]static void throw(Parser * parser, IrrecoverableParseError err) {
    parser->caught_error_buff = err;
    longjmp(parser->catch_site, 1);
}

static bool parser_eof(Parser * parser) {
    return parser->index == parser->span.size - 1;
}

// return value is never null
static Token * parser_peek(Parser * parser) {
    return parser->span.data + parser->index;
}

static Token * parser_peek_by(Parser * parser, usize look_ahead) {
    if (look_ahead + parser->index >= parser->span.size) {
        return parser->span.data + parser->span.size - 1;
    }
    return parser->span.data + parser->index + look_ahead;
}

static bool parser_advance(Parser * parser) {
    if (parser_eof(parser)) return false;
    ++parser->index;
    return true;
}

static bool parser_advance_by(Parser * parser, usize count) {
    parser->index = MIN(parser->span.size - 1, parser->index + count);
    return parser_eof(parser);
}

static Token * parser_advance_if(Parser * parser, TokenType type) {
    Token * tok = parser_peek(parser);
    if (tok->type != type) {
        return nullptr;
    }
    parser_advance(parser);
    return tok;
}

static void parser_emit_error(Parser * parser, ParseError err) {
    if (!parse_error_list_push(&parser->errors, err)) {
        throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
    }
    if (parser->errors.size >= MAX_TRANSLATION_UNIT_PARSE_ERRORS) {
        throw(parser, IRRECOVERABLE_PARSE_ERROR_LIMIT_REACHED);
    }
}

static bool parse_path(Parser * parser, PathBuilder * out) {
    PathBuilder path = {
        .is_global = false,
        .list = str_list_new(parser->allocator),
    };
    const Token * begin = parser_advance_if(parser, TOKEN_TYPE_SCOPE);
    if (begin) {
        path.is_global = true;
    }
    Token * fst_iden = parser_advance_if(parser, TOKEN_TYPE_IDENTIFIER);
    if (!fst_iden) {
        return false;
    }
    if (!begin) {
        begin = fst_iden;
    }
    if (!str_list_push(&path.list, token_get_str(*fst_iden, parser->src))) {
        throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
    }
    while (parser_advance_if(parser, TOKEN_TYPE_SCOPE)) {
        Token * iden = parser_advance_if(parser, TOKEN_TYPE_IDENTIFIER);
        if (!iden) {
            return false;
        }
        if (!str_list_push(&path.list, token_get_str(*iden, parser->src))) {
            throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
        }
    }
    path.span = extend_span_to(begin->span.pos, parser);
    *out = path;
    return true;
}

static bool parse_function_type_parameters(Parser * parser, AstTypeList * out) {
    if (!parser_advance_if(parser, TOKEN_TYPE_LPAREN)) {
        return false;
    }
    AstTypeList list = ast_type_list_new(parser->allocator);
    while (!parser_advance_if(parser, TOKEN_TYPE_RPAREN)) {
    parse_param:
        if (parser_eof(parser)) {
            return false;
        }
        AstFunParam param;
        if (!parse_function_param(parser, &param)) {
            parse_function_param_list_recover_invalid_param(parser);
            if (parser_advance_if(parser, TOKEN_TYPE_COMMA)) {
                goto parse_param;
            }
            continue;
        }
        if (!ast_type_list_push(&list, param.type)) {
            throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
        }
        if (parser_advance_if(parser, TOKEN_TYPE_COMMA)) {
            goto parse_param;
        } else if (parser_advance_if(parser, TOKEN_TYPE_RPAREN)) {
            break;
        } else {
            return false;
        }
    }
    *out = list;
    return true;
}

static AstType parse_function_type(Parser * parser) {
    const AstType poisoned = {.type = AST_TYPE_POISONED };
    Token * begin = parser_advance_if(parser, TOKEN_TYPE_FN);
    if (!begin) {
        return poisoned;
    }
    AstTypeList list;
    if (!parse_function_type_parameters(parser, &list)) {
        return poisoned;
    }
    bool has_return_type = false;
    AstType * return_type;
    if (parser_advance_if(parser, TOKEN_TYPE_COLON)) {
        has_return_type = true;
        return_type = allocator_alloc(parser->allocator, AstType);
        if (!return_type) {
            throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
        }
        *return_type = parse_type(parser);
        if (!type_is_ok(return_type)) {
            return poisoned;
        }
    }
    return (AstType) {
        .type = AST_TYPE_FN,
        .span = extend_span_to(begin->span.pos, parser),
        .function = {
            .has_return_type = has_return_type,
            .return_type = return_type,
            .parameters = ast_type_list_to_span(&list),
        }
    };
}

static AstType parse_type(Parser * parser) {
    const AstType poisoned = {.type = AST_TYPE_POISONED };
    Token * token = parser_peek(parser);
    switch (token->type) {
    {
        AstTypeType type;
    case TOKEN_TYPE_STAR:
        type = AST_TYPE_POINTER;
        goto next;
    case TOKEN_TYPE_AMPERSAND:
        type = AST_TYPE_REFERENCE;
        goto next;
    next:
        parser_advance(parser);
        AstType * next = allocator_alloc(parser->allocator, AstType);
        if (!next) {
            throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
        }
        *next = parse_type(parser);
        if (!type_is_ok(next)) {
            return poisoned;
        }
        return (AstType) {
            .type = type,
            .span = extend_span_to(token->span.pos, parser),
            .next = next,
        };
    }
    case TOKEN_TYPE_IDENTIFIER:
    case TOKEN_TYPE_SCOPE:
        PathBuilder path;
        if (!parse_path(parser, &path)) {
            return poisoned;
        }
        return (AstType) {
            .type = AST_TYPE_PATH,
            .span = extend_span_to(token->span.pos, parser),
            .path = path_builder_to_path(&path),
        };
    case TOKEN_TYPE_FN:
        return parse_function_type(parser);
    default:
        return poisoned;
    }
}

enum ExprInfixPrecedence {
    EXPR_PREC_NONE = 0,
    EXPR_PREC_AS,
    EXPR_PREC_TERM,
    EXPR_PREC_UNARY_POSTFIX,
    EXPR_PREC_PRIMARY,
} typedef ExprPrecedence;

static AstExpr parse_expr_with_precedence(Parser * parser, ExprPrecedence prec);

#define EXPR_LOW_PREC EXPR_PREC_AS
#define POISONED_EXPR ((AstExpr){ .type = AST_EXPR_POISONED })

struct ExprPrefixRule {
    AstExpr(*prefix)(Parser * parser);
    AstExpr(*infix)(Parser * parser, AstExpr prefix);
    ExprPrecedence prec;
} typedef ExprPrefixRule;

void parse_infix_funcall_recover_invalid_expr(Parser * parser) {
    while (!parser_eof(parser)) {
        Token * token = parser_peek(parser);
        switch (token->type) {
        case TOKEN_TYPE_COMMA:
        case TOKEN_TYPE_RPAREN:
            return;
        default:
            parser_advance(parser);
        }
    }
}

AstExpr parse_infix_funcall(Parser * parser, AstExpr expr) {
    if (!parser_advance_if(parser, TOKEN_TYPE_LPAREN)) {
        return POISONED_EXPR;
    }
    AstExprList list = ast_expr_list_new(parser->allocator);
    while (!parser_advance_if(parser, TOKEN_TYPE_RPAREN)) {
    parse_expr:
        if (parser_eof(parser)) {
            return POISONED_EXPR;
        }
        AstExpr expr = parse_expr(parser);
        if (!expr_is_ok(&expr)) {
            parse_infix_funcall_recover_invalid_expr(parser);
            if (parser_advance_if(parser, TOKEN_TYPE_COMMA)) {
                goto parse_expr;
            }
            continue;
        }
        if (!ast_expr_list_push(&list, expr)) {
            throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
        }
    }
    AstExpr * next = allocator_alloc(parser->allocator, AstExpr);
    if (!next) {
        throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
    }
    *next = expr;
    return (AstExpr) {
        .type = AST_EXPR_FUNCALL,
        .funcall = {
            .function = next,
            .args = ast_expr_list_to_span(&list),
        }
    };
}

AstExpr parse_infix_minus(Parser * parser, AstExpr expr) {
    if (!parser_advance_if(parser, TOKEN_TYPE_MINUS)) {
        return POISONED_EXPR;
    }
    AstExpr expr2 = parse_expr_with_precedence(parser, EXPR_PREC_TERM);
    if (!expr_is_ok(&expr2)) {
        return expr2;
    }
    AstExpr * a = allocator_alloc(parser->allocator, AstExpr);
    AstExpr * b = allocator_alloc(parser->allocator, AstExpr);
    if (!a || !b) {
        throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
    }
    *a = expr;
    *b = expr2;
    return (AstExpr) {
        .type = AST_EXPR_BINARY,
        .binary = {
            .a = a,
            .b = b,
            .type = AST_EXPR_BINARY_SUB,
        }
    };
}

AstExpr parse_infix_plus(Parser * parser, AstExpr expr) {
    if (!parser_advance_if(parser, TOKEN_TYPE_PLUS)) {
        return POISONED_EXPR;
    }
    AstExpr expr2 = parse_expr_with_precedence(parser, EXPR_PREC_TERM);
    if (!expr_is_ok(&expr2)) {
        return expr2;
    }
    AstExpr * a = allocator_alloc(parser->allocator, AstExpr);
    AstExpr * b = allocator_alloc(parser->allocator, AstExpr);
    if (!a || !b) {
        throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
    }
    *a = expr;
    *b = expr2;
    return (AstExpr) {
        .type = AST_EXPR_BINARY,
        .binary = {
            .a = a,
            .b = b,
            .type = AST_EXPR_BINARY_ADD,
        }
    };
}

AstExpr parse_infix_dot(Parser * parser, AstExpr expr) {
    if (!parser_advance_if(parser, TOKEN_TYPE_DOT)) {
        return POISONED_EXPR;
    }
    PathBuilder path;
    if (!parse_path(parser, &path)) {
        return POISONED_EXPR;
    }
    AstExpr * next = allocator_alloc(parser->allocator, AstExpr);
    if (!next) {
        throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
    }
    *next = expr;
    return (AstExpr) {
        .type = AST_EXPR_FIELD_ACCESS,
        .field_access = {
            .next = next,
            .name = path_builder_to_path(&path),
        }
    };
}

AstExpr parse_infix_dotstar(Parser * parser, AstExpr expr) {
    if (!parser_advance_if(parser, TOKEN_TYPE_DOTSTAR)) {
        return POISONED_EXPR;
    }
    AstExpr * next = allocator_alloc(parser->allocator, AstExpr);
    if (next == nullptr) {
        throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
    }
    *next = expr;
    AstExpr toret = (AstExpr) {
        .type = AST_EXPR_UNARY,
        .unary = {
            .next = next,
            .type = AST_EXPR_UNARY_DEREF,
        }
    };
    TokenType next_type = parser_peek(parser)->type;
    if (next_type == TOKEN_TYPE_SCOPE || next_type == TOKEN_TYPE_IDENTIFIER) {
        PathBuilder path;
        if (!parse_path(parser, &path)) {
            return POISONED_EXPR;
        }
        AstExpr * next = allocator_alloc(parser->allocator, AstExpr);
        if (next == nullptr) {
            throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
        }
        *next = toret;
        toret = (AstExpr) {
            .type = AST_EXPR_FIELD_ACCESS,
            .field_access = {
                .next = next,
                .name = path_builder_to_path(&path),
            }
        };
    }
    return toret;
}

AstExpr parse_infix_as(Parser * parser, AstExpr expr) {
    if (!parser_advance_if(parser, TOKEN_TYPE_AS)) {
        return POISONED_EXPR;
    }
    AstType type = parse_type(parser);
    if (type.type == AST_TYPE_POISONED) {
        return POISONED_EXPR;
    }
    AstExpr * next = allocator_alloc(parser->allocator, AstExpr);
    if (!next) {
        throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
    }
    *next = expr;
    return (AstExpr) {
        .type = AST_EXPR_AS,
        .as = {
            .next = next,
            .type = type,
        }
    };
}

AstExpr parse_prefix_path(Parser * parser) {
    PathBuilder path;
    if (!parse_path(parser, &path)) {
        return POISONED_EXPR;
    }
    return (AstExpr) {
        .type = AST_EXPR_PATH,
        .path = path_builder_to_path(&path),
    };
}

AstExpr parse_prefix_fn(Parser * parser) {
    if (!parser_advance_if(parser, TOKEN_TYPE_FN)) {
        return POISONED_EXPR;
    }
    AstFunParamList params;
    if (!parse_function_param_list(parser, &params)) {
        return POISONED_EXPR;
    }
    bool has_return = false;
    AstType return_type;
    if (parser_advance_if(parser, TOKEN_TYPE_COLON)) {
        has_return = true;
        return_type = parse_type(parser);
        if (!type_is_ok(&return_type)) {
            parse_function_recover_invalid_return_type(parser);
        }
    }
    AstStmtList body;
    if (!parse_stmt_block(parser, &body)) {
        return POISONED_EXPR;
    }
    AstFunction * function = allocator_alloc(parser->allocator, AstFunction);
    if (!function) {
        throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
    }
    *function = (AstFunction) {
        .params = ast_fun_param_list_to_span(&params),
        .has_return_type = has_return,
        .return_type = return_type,
        .body = ast_stmt_list_to_span(&body),
    };
    return (AstExpr) {
        .type = AST_EXPR_FUNCTION,
        .function = function,
    };
}

AstExpr parse_prefix_lparen(Parser * parser) {
    if (!parser_advance_if(parser, TOKEN_TYPE_LPAREN)) {
        return POISONED_EXPR;
    }
    AstExpr expr = parse_expr(parser);
    if (expr.type == AST_EXPR_POISONED) {
        parser_emit_error(parser, (ParseError) {
            .unexpected_token = *parser_peek(parser),
        });
        while (!parser_eof(parser)) {
            switch (parser_peek(parser)->type) {
            case TOKEN_TYPE_RPAREN:
                parser_advance(parser);
                goto outer;
            case TOKEN_TYPE_SEMICOLON:
                goto outer;
            default:
                parser_advance(parser);
            }
        }
    outer:
        expr.type = AST_EXPR_POISONED_NESTED;
        return expr;
    }
    if (!parser_advance_if(parser, TOKEN_TYPE_RPAREN)) {
        return POISONED_EXPR;
    }
    return expr;
}

AstExpr parse_prefix_integer(Parser * parser) {
    Token * token = parser_advance_if(parser, TOKEN_TYPE_INTEGER);
    if (!token) {
        return POISONED_EXPR;
    }
    usize n = 0;
    Str slice = token_get_str(*token, parser->src);
    Writer stderrw = stderr_writer();
    foreach_span(&slice, i) {
        n = 10 * n + (*i - '0');
    }
    return (AstExpr) {
        .type = AST_EXPR_INTEGER,
        .integer = {
            .value = n
        }
    };
}

AstExpr parse_prefix_plus(Parser * parser) {
    if (!parser_advance_if(parser, TOKEN_TYPE_PLUS)) {
        return POISONED_EXPR;
    }
    return parse_expr_with_precedence(parser, EXPR_PREC_UNARY_POSTFIX);
}

AstExpr parse_prefix_minus(Parser * parser) {
    if (!parser_advance_if(parser, TOKEN_TYPE_AMPERSAND)) {
        return POISONED_EXPR;
    }
    AstExpr expr = parse_expr_with_precedence(parser, EXPR_PREC_UNARY_POSTFIX);
    if (!expr_is_ok(&expr)) {
        return expr;
    }
    AstExpr * next = allocator_alloc(parser->allocator, AstExpr);
    if (!next) {
        throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
    }
    *next = expr;
    return (AstExpr) {
        .type = AST_EXPR_UNARY,
        .unary = {
            .next = next,
            .type = AST_EXPR_UNARY_MINUS,
        }
    };
}

AstExpr parse_prefix_ampersand(Parser * parser) {
    if (!parser_advance_if(parser, TOKEN_TYPE_AMPERSAND)) {
        return POISONED_EXPR;
    }
    AstExpr expr = parse_expr_with_precedence(parser, EXPR_PREC_UNARY_POSTFIX);
    if (!expr_is_ok(&expr)) {
        return expr;
    }
    AstExpr * next = allocator_alloc(parser->allocator, AstExpr);
    if (!next) {
        throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
    }
    *next = expr;
    return (AstExpr) {
        .type = AST_EXPR_UNARY,
        .unary = {
            .next = next,
            .type = AST_EXPR_UNARY_ADDR,
        }
    };
}

ExprPrefixRule expr_pratt_rules[TOKEN_TYPE_EOF] = {
    [TOKEN_TYPE_LPAREN] = {parse_prefix_lparen, parse_infix_funcall, EXPR_PREC_UNARY_POSTFIX},
    [TOKEN_TYPE_IDENTIFIER] = {parse_prefix_path, nullptr, EXPR_PREC_NONE},
    [TOKEN_TYPE_SCOPE] = {parse_prefix_path, nullptr, EXPR_PREC_NONE},
    [TOKEN_TYPE_INTEGER] = {parse_prefix_integer, nullptr, EXPR_PREC_NONE},
    [TOKEN_TYPE_FN] = {parse_prefix_fn, nullptr, EXPR_PREC_NONE},
    [TOKEN_TYPE_AS] = {nullptr, parse_infix_as, EXPR_PREC_AS},
    [TOKEN_TYPE_PLUS] = {parse_prefix_plus, parse_infix_plus, EXPR_PREC_TERM},
    [TOKEN_TYPE_MINUS] = {parse_prefix_minus, parse_infix_minus, EXPR_PREC_TERM},
    [TOKEN_TYPE_AMPERSAND] = {parse_prefix_ampersand, nullptr, EXPR_PREC_NONE},
    [TOKEN_TYPE_DOTSTAR] = {nullptr, parse_infix_dotstar, EXPR_PREC_UNARY_POSTFIX},
    [TOKEN_TYPE_DOT] = {nullptr, parse_infix_dot, EXPR_PREC_UNARY_POSTFIX},
};

static AstExpr parse_expr_with_precedence(Parser * parser, ExprPrecedence prec) {
    Token * token = parser_peek(parser);
    ExprPrefixRule * rule = expr_pratt_rules + token->type;
    if (!rule->prefix) {
        return POISONED_EXPR;
    }
    AstExpr expr = rule->prefix(parser);
    while (expr_is_ok(&expr)) {
        Token * token = parser_peek(parser);
        ExprPrefixRule * rule = expr_pratt_rules + token->type;
        if (prec > rule->prec) {
            break;
        }
        if (!rule->infix) {
            return POISONED_EXPR;
        }
        expr = rule->infix(parser, expr);
    }
    expr.span = extend_span_to(token->span.pos, parser);
    return expr;
}

static AstExpr parse_expr(Parser * parser) {
    return parse_expr_with_precedence(parser, EXPR_LOW_PREC);
}


static void parse_stmt_recover_to_next_stmt(Parser * parser) {
    parser_emit_error(parser, (ParseError) {
        *parser_peek(parser)
    });
    while (!parser_eof(parser)) {
        const Token * const token = parser_peek(parser);
        switch (token->type) {
        case TOKEN_TYPE_RBRACE:
            return;
        default:
            parser_advance(parser);
        }
    }
}

// return type test for semicolon
static bool parse_stmt(Parser * parser, AstStmt * out) {
    const AstStmt poisoned = {.type = AST_STMT_POISONED};
    Token * token = parser_peek(parser);
    switch (token->type) {
    case TOKEN_TYPE_SEMICOLON:
        parser_advance(parser);
        return false;
    case TOKEN_TYPE_RETURN:
        parser_advance(parser);
        bool has_return_expr = false;
        AstExpr return_expr;
        if (!parser_advance_if(parser, TOKEN_TYPE_SEMICOLON)) {
            has_return_expr = true;
            return_expr = parse_expr(parser);
            if (!expr_is_ok(&return_expr)) {
                goto error;
            }
            if (!parser_advance_if(parser, TOKEN_TYPE_SEMICOLON)) {
                goto error;
            }
        }
        *out = (AstStmt) {
            .type = AST_STMT_RETURN,
            .span = extend_span_to(token->span.pos, parser),
            .has_return_expr = has_return_expr,
            .return_expr = return_expr,
        };
        return true;
    case TOKEN_TYPE_FN:
        AstDecl * decl = allocator_alloc(parser->allocator, AstDecl);
        if (!decl) {
            throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
        }
        if (!parse_function(parser, decl)) {
            goto error;
        }
        *out = (AstStmt) {
            .type = AST_STMT_DECL,
            .span = extend_span_to(token->span.pos, parser),
            .decl = decl,
        };
        return true;
    case TOKEN_TYPE_LET:
    case TOKEN_TYPE_CONST:
            decl = allocator_alloc(parser->allocator, AstDecl);
            if (!decl) {
                throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
            }
            if (!parse_decl(parser, decl)) {
                goto error;
            }
            *out = (AstStmt) {
                .type = AST_STMT_DECL,
                .span = extend_span_to(token->span.pos, parser),
                .decl = decl,
            };
            return true;
    case TOKEN_TYPE_LBRACE:
        AstStmtList list = ast_stmt_list_new(parser->allocator);
        if (!parse_stmt_block(parser, &list)) {
            goto error;
        }
        *out = (AstStmt) {
            .type = AST_STMT_BLOCK,
            .span = extend_span_to(token->span.pos, parser),
            .block = ast_stmt_list_to_span(&list),
        };
        return true;
    default:
        AstExpr expr = parse_expr(parser);
        if (!expr_is_ok(&expr)) {
            goto error;
        }
        if (!parser_advance_if(parser, TOKEN_TYPE_EQ)) {
            if (!parser_advance_if(parser, TOKEN_TYPE_SEMICOLON)) {
                goto error;
            }
            *out = (AstStmt) {
                .type = AST_STMT_EXPR,
                .span = extend_span_to(token->span.pos, parser),
                .expr = expr,
            };
            return true;
        }
        AstExpr expr2 = parse_expr(parser);
        if (!expr_is_ok(&expr2)) {
            goto error;
        }
        if (!parser_advance_if(parser, TOKEN_TYPE_SEMICOLON)) {
            goto error;
        }
        *out = (AstStmt) {
            .type = AST_STMT_ASSIGNMENT,
            .span = extend_span_to(token->span.pos, parser),
            .assign = {
                .to = expr,
                .from = expr2,
            }
        };
        return true;
    error:
        *out = poisoned;
        return true;
    }
}

static bool parse_function_param(Parser * parser, AstFunParam * out) {
    Token * token = parser_peek(parser);
    AstFunParam param;
    if (token->type == TOKEN_TYPE_IDENTIFIER && parser_peek_by(parser, 1)->type == TOKEN_TYPE_COLON) {
        parser_advance_by(parser, 2);
        param.iden = token_get_str(*token, parser->src);
    } else {
        param.iden = EMPTY_STR;
    }
    param.type = parse_type(parser);
    if (!type_is_ok(&param.type)) {
        return false;
    }
    param.span = extend_span_to(token->span.pos, parser);
    *out = param;
    return true;
}

static void parse_function_param_list_recover_invalid_param(Parser * parser) {
    parser_emit_error(parser, (ParseError) {
        *parser_peek(parser)
    });
    while (!parser_eof(parser)) {
        const Token * const token = parser_peek(parser);
        switch (token->type) {
        case TOKEN_TYPE_COMMA:
        case TOKEN_TYPE_RPAREN:
            return;
        default:
            parser_advance(parser);
        }
    }
}

static bool parse_function_param_list(Parser * parser, AstFunParamList * out) {
    if (!parser_advance_if(parser, TOKEN_TYPE_LPAREN)) {
        return false;
    }
    AstFunParamList list = ast_fun_param_list_new(parser->allocator);
    while (!parser_advance_if(parser, TOKEN_TYPE_RPAREN)) {
    parse_param:
        if (parser_eof(parser)) {
            return false;
        }
        AstFunParam param;
        if (!parse_function_param(parser, &param)) {
            parse_function_param_list_recover_invalid_param(parser);
            if (parser_advance_if(parser, TOKEN_TYPE_COMMA)) {
                goto parse_param;
            }
            continue;
        }
        if (!ast_fun_param_list_push(&list, param)) {
            throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
        }
        if (parser_advance_if(parser, TOKEN_TYPE_COMMA)) {
            goto parse_param;
        } else if (parser_advance_if(parser, TOKEN_TYPE_RPAREN)) {
            break;
        } else {
            return false;
        }
    }
    *out = list;
    return true;
}

static void parse_function_body_recover_invalid_stmt(Parser * parser) {
    parser_emit_error(parser, (ParseError) {
        *parser_peek(parser)
    });
    while (!parser_eof(parser)) {
        const Token * const token = parser_peek(parser);
        switch (token->type) {
        case TOKEN_TYPE_RBRACE:
        case TOKEN_TYPE_SEMICOLON:
            return;
        default:
            parser_advance(parser);
        }
    }
}

static bool parse_stmt_block(Parser * parser, AstStmtList * out) {
    if (!parser_advance_if(parser, TOKEN_TYPE_LBRACE)) {
        return false;
    }
    AstStmtList list = ast_stmt_list_new(parser->allocator);
    while (!parser_advance_if(parser, TOKEN_TYPE_RBRACE)) {
        AstStmt stmt;
        if (!parse_stmt(parser, &stmt)) {
            continue;
        }
        if (stmt.type == AST_STMT_POISONED) {
            parse_function_body_recover_invalid_stmt(parser);
            continue;
        }
        if (!ast_stmt_list_push(&list, stmt)) {
            throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
        }
    }
    *out = list;
    return true;
}

static void parse_function_recover_invalid_return_type(Parser * parser) {
    parser_emit_error(parser, (ParseError) {
        *parser_peek(parser)
    });
    while (!parser_eof(parser)) {
        const Token * const token = parser_peek(parser);
        switch (token->type) {
        case TOKEN_TYPE_LBRACE:
            return;
        default:
            parser_advance(parser);
        }
    }
}

static bool parse_function(Parser * parser, AstDecl * out) {
    AstDecl decl = {
        .is_const = true,
        .has_type = false,
        .has_expr = true,
    };
    const Token * begin = parser_advance_if(parser, TOKEN_TYPE_FN);
    if (!begin) {
        return false;
    }
    Token * iden_token = parser_advance_if(parser, TOKEN_TYPE_IDENTIFIER);
    if (!iden_token) {
        return false;
    }
    decl.iden = token_get_str(*iden_token, parser->src);
    AstFunction function;
    AstFunParamList list;
    if (!parse_function_param_list(parser, &list)) {
        return false;
    }
    function.params = ast_fun_param_list_to_span(&list);
    if (parser_advance_if(parser, TOKEN_TYPE_COLON)) {
        function.has_return_type = true;
        function.return_type = parse_type(parser);
        if (!type_is_ok(&function.return_type)) {
            parse_function_recover_invalid_return_type(parser);
        }
    } else {
        function.has_return_type = false;
    }
    AstStmtList body;
    if (!parse_stmt_block(parser, &body)) {
        return false;
    }
    function.body = ast_stmt_list_to_span(&body);
    AstFunction * fun_alloc = allocator_alloc(parser->allocator, AstFunction);
    if (!fun_alloc) {
        throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
    }
    *fun_alloc = function;
    decl.expr = (AstExpr) {
        .type = AST_EXPR_FUNCTION,
        .span = extend_span_to(begin->span.pos, parser),
        .function = fun_alloc,
    };
    *out = decl;
    return true;
}

static void parse_decl_recover_invalid_type(Parser * parser) {
    parser_emit_error(parser, (ParseError) {
        *parser_peek(parser)
    });
    while (!parser_eof(parser)) {
        const Token * const token = parser_peek(parser);
        switch (token->type) {
        case TOKEN_TYPE_SEMICOLON:
        case TOKEN_TYPE_EQ:
            return;
        default:
            parser_advance(parser);
        }
    }
}

static void parse_decl_recover_invalid_expr(Parser * parser) {
    parser_emit_error(parser, (ParseError) {
        *parser_peek(parser)
    });
    while (!parser_eof(parser)) {
        const Token * const token = parser_peek(parser);
        switch (token->type) {
        case TOKEN_TYPE_SEMICOLON:
            return;
        default:
            parser_advance(parser);
        }
    }
}

static bool parse_decl(Parser * parser, AstDecl * out) {
    AstDecl decl;
    bool is_const;
    const Token * begin = parser_advance_if(parser, TOKEN_TYPE_LET);
    if (begin) {
        decl.is_const = false;
    } else if  ((begin = parser_advance_if(parser, TOKEN_TYPE_CONST))) {
        decl.is_const = true;
    } else {
        return false;
    }
    Token * iden_token = parser_advance_if(parser, TOKEN_TYPE_IDENTIFIER);
    if (!iden_token) {
        return false;
    }
    decl.iden = token_get_str(*iden_token, parser->src);
    if (parser_advance_if(parser, TOKEN_TYPE_COLON)) {
        decl.type = parse_type(parser);
        if (!type_is_ok(&decl.type)) {
            parse_decl_recover_invalid_type(parser);
        }
        decl.has_type = true;
    } else {
        decl.has_type = false;
    }
    if (parser_advance_if(parser, TOKEN_TYPE_EQ)) {
        decl.has_expr = true;
        decl.expr = parse_expr(parser);
        if (!expr_is_ok(&decl.expr)) {
            parse_decl_recover_invalid_expr(parser);
        }
    } else {
        decl.has_expr = false;
    }
    if (!parser_advance_if(parser, TOKEN_TYPE_SEMICOLON)) {
        return false;
    }
    decl.span = extend_span_to(begin->span.pos, parser);
    *out = decl;
    return true;
}

static bool parse_mod(Parser * parser, AstModule * out) {
    const Token * begin = parser_advance_if(parser, TOKEN_TYPE_MOD);
    if (!begin) {
        return false;
    }
    Token * iden_token = parser_advance_if(parser, TOKEN_TYPE_IDENTIFIER);
    if (!iden_token) {
        return false;
    }
    Str iden = token_get_str(*iden_token, parser->src);
    if (!parser_advance_if(parser, TOKEN_TYPE_LBRACE)) {
        return false;
    }
    AstTLSList list = ast_tls_list_new(parser->allocator);
    while (parser_advance_if(parser, TOKEN_TYPE_RBRACE) == nullptr) {
        if (parser_eof(parser)) {
            return false;
        }
        AstTopLvlStmt tls;
        if (!parse_tls(parser, &tls)) {
            continue;
        }
        if (tls.type == AST_TLS_TYPE_POISONED) {
            recover_nested(parser);
            continue;
        }
        if (!ast_tls_list_push(&list, tls)) {
            throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
        }
    }
    *out = (AstModule) {
        .span = extend_span_to(begin->span.pos, parser),
        .iden = iden,
        .body = ast_tls_list_to_span(&list),
    };
    return true;
}

// return value could be null in case of parsing a semicolon.
static bool parse_tls(Parser * parser, AstTopLvlStmt * out) {
    static const AstTopLvlStmt poisoned = { .type = AST_TLS_TYPE_POISONED };
    Token * const token = parser_peek(parser);
    if (token->type == TOKEN_TYPE_SEMICOLON) {
        parser_advance(parser);
        return false;
    }
    AstTopLvlStmt tls;
    switch (token->type) {
    case TOKEN_TYPE_MOD:
        tls = (AstTopLvlStmt) {
            .type = AST_TLS_TYPE_MOD,
        };
        if (!parse_mod(parser, &tls.mod)) {
            *out = poisoned;
            return true;
        }
        break;
    case TOKEN_TYPE_FN:
        tls = (AstTopLvlStmt) {
            .type = AST_TLS_TYPE_DECL,
        };
        if (!parse_function(parser, &tls.decl)) {
            *out = poisoned;
            return true;
        }
        break;
    case TOKEN_TYPE_LET:
    case TOKEN_TYPE_CONST:
        tls = (AstTopLvlStmt) {
            .type = AST_TLS_TYPE_DECL,
        };
        if (!parse_decl(parser, &tls.decl)) {
            *out = poisoned;
            return true;
        }
        break;
    default:
        *out = poisoned;
        return true;
    }
    tls.span = extend_span_to(token->span.pos, parser);
    *out = tls;
    return true;
}

static void recover_nested(Parser * parser) {
    Token * token = parser_peek(parser);
    parser_emit_error(parser, (ParseError) {
        .unexpected_token = *token
    });
    while (!parser_eof(parser)) {
        Token * const token = parser_peek(parser);
        switch (token->type) {
        case TOKEN_TYPE_MOD:
        case TOKEN_TYPE_FN:
        case TOKEN_TYPE_LET:
        case TOKEN_TYPE_CONST:
        case TOKEN_TYPE_RBRACE:
            return;
        default:
            parser_advance(parser);
        }
    }
}

static void recover_top_lvl(Parser * parser) {
    Token * token = parser_peek(parser);
    parser_emit_error(parser, (ParseError) {
        .unexpected_token = *token
    });
    while (!parser_eof(parser)) {
        Token * const token = parser_peek(parser);
        switch (token->type) {
        case TOKEN_TYPE_MOD:
        case TOKEN_TYPE_FN:
        case TOKEN_TYPE_LET:
        case TOKEN_TYPE_CONST:
            return;
        default:
            parser_advance(parser);
        }
    }
}

ParseResult parse(Allocator allocator, Str src, TokenSpan tokens) {
    Parser parser;
    jmp_buf buff;
    if (setjmp(buff)) {
        return (ParseResult) {
            .irrecoverable = true,
            .irrecoverable_error = parser.caught_error_buff,
            .errors = parser.errors,
        };
    }
    parser = (Parser) {
        .src = src,
        .span = tokens,
        .index = 0,
        .errors = parse_error_list_new(allocator),
        .catch_site = *buff,
        .allocator = allocator,
    };
    AstTLSList list = ast_tls_list_new(allocator);
    Token * token;
    while ((token = parser_peek(&parser))->type != TOKEN_TYPE_EOF) {
        AstTopLvlStmt tls;
        if (!parse_tls(&parser, &tls)) continue;
        if (tls.type == AST_TLS_TYPE_POISONED) {
            recover_top_lvl(&parser);
            continue;
        }
        if (!ast_tls_list_push(&list, tls)) {
            throw(&parser, IRRECOVERABLE_PARSE_ERROR_OOM);
        }
    }
    return (ParseResult) {
        .irrecoverable = false,
        .ast = (Ast){
            ast_tls_list_to_span(&list)
        },
        .errors = parser.errors,
    };
}
