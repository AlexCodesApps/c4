#include "include/ast.h"
#include "include/allocator.h"
#include "include/generic/darray.h"
#include "include/lexer.h"
#include "include/str.h"
#include <setjmp.h>

static void recover_nested(Parser * parser);
static const AstTopLvlStmt * parse_tls(Parser * parser);
static bool parse_function(Parser * parser, AstDecl * out);
static bool parse_decl(Parser * parser, AstDecl * out);
static bool parse_stmt_block(Parser * parser, AstStmtList * out);
static bool parse_function_param(Parser * parser, AstFunParam * out);
static void parse_function_param_list_recover_invalid_param(Parser * parser);
static void parse_function_recover_invalid_return_type(Parser * parser);
static bool parse_function_param_list(Parser * parser, AstFunParamList * out);
static AstType parse_type(Parser * parser);
static AstExpr parse_expr(Parser * parser);

static bool expr_is_ok(AstExpr * expr) {
    return expr->type != AST_EXPR_POISONED;
}
bool type_is_ok(AstType * type) {
    return type->type != AST_TYPE_POISONED;
}

DARRAY_IMPL(AST_TYPE_LIST_TEMPLATE);
DARRAY_IMPL(AST_TOP_LVL_STMT_LIST_TEMPLATE);
DARRAY_IMPL(AST_ERROR_LIST_TEMPLATE);
DARRAY_IMPL(AST_FUN_PARAM_LIST_TEMPLATE);
DARRAY_IMPL(AST_STMT_LIST_TEMPLATE);
DARRAY_IMPL(AST_EXPR_LIST_TEMPLATE);
DARRAY_IMPL(AST_PATH_TEMPLATE);

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

static bool parse_path(Parser * parser, AstPath * out) {
    AstPath path = {
        .is_global = false,
        .list = ast_path_list_new(parser->allocator),
    };
    if (parser_advance_if(parser, TOKEN_TYPE_SCOPE)) {
        path.is_global = true;
    }
    Token * fst = parser_advance_if(parser, TOKEN_TYPE_IDENTIFIER);
    if (!fst) {
        return false;
    }
    if (!ast_path_list_push(&path.list, token_get_str(*fst, parser->src))) {
        throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
    }
    while (parser_advance_if(parser, TOKEN_TYPE_SCOPE)) {
        Token * iden = parser_advance_if(parser, TOKEN_TYPE_IDENTIFIER);
        if (!iden) {
            return false;
        }
        if (!ast_path_list_push(&path.list, token_get_str(*iden, parser->src))) {
            throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
        }
    }
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
    if (!parser_advance_if(parser, TOKEN_TYPE_FN)) {
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
        if (return_type->type == AST_TYPE_POISONED) {
            return poisoned;
        }
    }
    return (AstType) {
        .type = AST_TYPE_FN,
        .function = {
            .has_return_type = has_return_type,
            .return_type = return_type,
            .parameters = list,
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
            .next = next,
        };
    }
    case TOKEN_TYPE_IDENTIFIER:
    case TOKEN_TYPE_SCOPE:
        AstPath path;
        if (!parse_path(parser, &path)) {
            return poisoned;
        }
        return (AstType) {
            .type = AST_TYPE_PATH,
            .path = path,
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
#define POISONED_EXPR (AstExpr){ .type = AST_EXPR_POISONED }

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
            .args = list,
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
    AstPath path;
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
            .name = path,
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
        .type = AST_EXPR_BINARY,
        .unary = {
            .next = next,
            .type = AST_EXPR_UNARY_DEREF,
        }
    };
    TokenType next_type = parser_peek(parser)->type;
    if (next_type == TOKEN_TYPE_SCOPE || next_type == TOKEN_TYPE_IDENTIFIER) {
        AstPath path;
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
                .name = path,
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
    AstPath path;
    if (!parse_path(parser, &path)) {
        return POISONED_EXPR;
    }
    return (AstExpr) {
        .type = AST_EXPR_PATH,
        .path = path,
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
        .params = params,
        .has_return_type = has_return,
        .return_type = return_type,
        .body = body,
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
        while (!parser_eof(parser)) {
            switch (parser_peek(parser)->type) {
            case TOKEN_TYPE_RPAREN:
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
    foreach_str(&slice, i) {
        n = 10 * n + (*i - '\0');
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

ExprPrefixRule expr_pratt_rules[TOKEN_TYPE_EOF + 1] = {
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
            if (return_expr.type == AST_EXPR_POISONED) {
                goto error;
            }
            if (!parser_advance_if(parser, TOKEN_TYPE_SEMICOLON)) {
                goto error;
            }
        }
        *out = (AstStmt) {
            .type = AST_STMT_RETURN,
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
            .block = list,
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
                .expr = expr,
            };
            return true;
        }
        AstExpr expr2 = parse_expr(parser);
        if (expr2.type == AST_EXPR_POISONED) {
            goto error;
        }
        if (!parser_advance_if(parser, TOKEN_TYPE_SEMICOLON)) {
            goto error;
        }
        *out = (AstStmt) {
            .type = AST_STMT_ASSIGNMENT,
            .assign_to = expr,
            .assign_from = expr,
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
    if (!parser_advance_if(parser, TOKEN_TYPE_FN)) {
        return false;
    }
    Token * iden_token = parser_advance_if(parser, TOKEN_TYPE_IDENTIFIER);
    if (!iden_token) {
        return false;
    }
    decl.iden = str_slice(parser->src, iden_token->span.pos.index, iden_token->span.len);
    AstFunction function;
    if (!parse_function_param_list(parser, &function.params)) {
        return false;
    }
    if (parser_advance_if(parser, TOKEN_TYPE_COLON)) {
        function.has_return_type = true;
        function.return_type = parse_type(parser);
        if (function.return_type.type == AST_TYPE_POISONED) {
            parse_function_recover_invalid_return_type(parser);
        }
    } else {
        function.has_return_type = false;
    }
    if (!parse_stmt_block(parser, &function.body)) {
        return false;
    }
    AstFunction * fun_alloc = allocator_alloc(parser->allocator, AstFunction);
    if (!fun_alloc) {
        throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
    }
    *fun_alloc = function;
    decl.expr = (AstExpr) {
        .type = AST_EXPR_FUNCTION,
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
    if (parser_advance_if(parser, TOKEN_TYPE_LET)) {
        decl.is_const = false;
    } else if  (parser_advance_if(parser, TOKEN_TYPE_CONST)) {
        decl.is_const = true;
    } else {
        return false;
    }
    Token * iden_token = parser_advance_if(parser, TOKEN_TYPE_IDENTIFIER);
    if (!iden_token) {
        return false;
    }
    decl.iden = str_slice(parser->src, iden_token->span.pos.index, iden_token->span.len);
    if (parser_advance_if(parser, TOKEN_TYPE_COLON)) {
        decl.type = parse_type(parser);
        if (decl.type.type == AST_TYPE_POISONED) {
            parse_decl_recover_invalid_type(parser);
        }
        decl.has_type = true;
    } else {
        decl.has_type = false;
    }
    if (parser_advance_if(parser, TOKEN_TYPE_EQ)) {
        decl.has_expr = true;
        decl.expr = parse_expr(parser);
        if (decl.expr.type == AST_EXPR_POISONED) {
            parse_decl_recover_invalid_expr(parser);
        }
    } else {
        decl.has_expr = false;
    }
    if (!parser_advance_if(parser, TOKEN_TYPE_SEMICOLON)) {
        return false;
    }
    *out = decl;
    return true;
}

static bool parse_mod(Parser * parser, AstModule * out) {
    if (!parser_advance_if(parser, TOKEN_TYPE_MOD)) {
        return false;
    }
    Token * iden_token = parser_advance_if(parser, TOKEN_TYPE_IDENTIFIER);
    if (!iden_token) {
        return false;
    }
    Str iden = str_slice(parser->src, iden_token->span.pos.index, iden_token->span.len);
    if (!parser_advance_if(parser, TOKEN_TYPE_LBRACE)) {
        return false;
    }
    AstTLSList list = ast_tls_list_new(parser->allocator);
    while (parser_advance_if(parser, TOKEN_TYPE_RBRACE) == nullptr) {
        if (parser_eof(parser)) {
            return false;
        }
        const AstTopLvlStmt * tls = parse_tls(parser);
        if (!tls) continue;
        if (tls->type == AST_TLS_TYPE_POISONED) {
            recover_nested(parser);
            continue;
        }
        if (!ast_tls_list_push(&list, tls)) {
            throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
        }
    }
    *out = (AstModule) {
        .iden = iden,
        .body = list,
    };
    return true;
}

// return value could be null in case of parsing a semicolon.
static const AstTopLvlStmt * parse_tls(Parser * parser) {
    static const AstTopLvlStmt poisoned_value = { .type = AST_TLS_TYPE_POISONED };
    const AstTopLvlStmt * const poisoned = &poisoned_value;
    Token * const token = parser_peek(parser);
    if (token->type == TOKEN_TYPE_SEMICOLON) {
        parser_advance(parser);
        return nullptr;
    }
    AstTopLvlStmt * const tls = allocator_alloc(parser->allocator, AstTopLvlStmt);
    if (!tls) {
        throw(parser, IRRECOVERABLE_PARSE_ERROR_OOM);
    }
    switch (token->type) {
    case TOKEN_TYPE_MOD:
        *tls = (AstTopLvlStmt) {
            .type = AST_TLS_TYPE_MOD,
        };
        if (!parse_mod(parser, &tls->mod)) {
            return poisoned;
        }
        break;
    case TOKEN_TYPE_FN:
        *tls = (AstTopLvlStmt) {
            .type = AST_TLS_TYPE_DECL,
        };
        if (!parse_function(parser, &tls->decl)) {
            return poisoned;
        }
        break;
    case TOKEN_TYPE_LET:
    case TOKEN_TYPE_CONST:
        *tls = (AstTopLvlStmt) {
            .type = AST_TLS_TYPE_DECL,
        };
        if (!parse_decl(parser, &tls->decl)) {
            return poisoned;
        }
        break;
    default:
        return poisoned;
    }
    return tls;
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
        const AstTopLvlStmt * tls = parse_tls(&parser);
        if (!tls) continue;
        if (tls->type == AST_TLS_TYPE_POISONED) {
            recover_top_lvl(&parser);
            continue;
        }
        if (!ast_tls_list_push(&list, tls)) {
            throw(&parser, IRRECOVERABLE_PARSE_ERROR_OOM);
        }
    }
    return (ParseResult) {
        .irrecoverable = false,
        .ast = (Ast){list},
        .errors = parser.errors,
    };
}
