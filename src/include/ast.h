#pragma once

#include "allocator.h"
#include "common.h"
#include "generic/darray.h"
#include "lexer.h"
#include "str.h"

enum AstTLSType {
    AST_TLS_POISONED,
    AST_TLS_DECL,
    AST_TLS_MOD,
    AST_TLS_STRUCT,
} typedef AstTLSType;

#define AST_TYPE_LIST_TEMPLATE(m) m(AstTypeList, ast_type_list, struct AstType)
DARRAY_HEADER(AST_TYPE_LIST_TEMPLATE);
struct AstTypeSpan {
    const struct AstType * data;
    usize size;
} typedef AstTypeSpan;

static AstTypeSpan ast_type_list_to_span(const AstTypeList list[ref]) {
    return (AstTypeSpan){
        .data = list->data,
        .size = list->size,
    };
}

enum AstTypeType : u8 {
    AST_TYPE_POISONED,
    AST_TYPE_POINTER,
    AST_TYPE_REFERENCE,
    AST_TYPE_FN,
    AST_TYPE_PATH,
    AST_TYPE_BUILTIN,
} typedef AstTypeType;

struct AstType {
    AstTypeType type;
    SrcSpan span;
    union {
        struct AstType * pointer;
        struct AstType * reference;
        Path path;
        struct {
            bool has_return_type;
            struct AstType * return_type;
            AstTypeSpan parameters;
        } function;
    } as;
} typedef AstType;

#define AST_EXPR_LIST_TEMPLATE(m) m(AstExprList, ast_expr_list, struct AstExpr)
DARRAY_HEADER(AST_EXPR_LIST_TEMPLATE);

struct AstExprSpan {
    const struct AstExpr * data;
    usize size;
} typedef AstExprSpan;

static AstExprSpan ast_expr_list_to_span(const AstExprList list[ref]) {
    return (AstExprSpan){
        .data = list->data,
        .size = list->size,
    };
}

enum AstExprBinaryType : u8 {
    AST_EXPR_BINARY_ADD,
    AST_EXPR_BINARY_SUB,
} typedef AstExprBinaryType;

enum AstExprUnaryType : u8 {
    AST_EXPR_UNARY_MINUS,
    AST_EXPR_UNARY_DEREF,
    AST_EXPR_UNARY_ADDR,
} typedef AstExprUnaryType;

enum AstExprType : u8 {
    AST_EXPR_FUNCTION,
    AST_EXPR_PATH,
    AST_EXPR_FUNCALL,
    AST_EXPR_POISONED,
    AST_EXPR_POISONED_NESTED,
    AST_EXPR_UNARY,
    AST_EXPR_BINARY,
    AST_EXPR_AS,
    AST_EXPR_INTEGER,
    AST_EXPR_FIELD_ACCESS,
    AST_EXPR_STRUCT_INIT,
} typedef AstExprType;

struct AstExprStructInitParam {
    SrcSpan span;
    Str iden;
    struct AstExpr * expr;
} typedef AstExprStructInitParam;

#define AST_EXPR_STRUCT_INIT_PARAM_LIST(m)                                     \
    m(AstExprStructInitParamList, ast_expr_struct_init_param_list,             \
      AstExprStructInitParam)
DARRAY_HEADER(AST_EXPR_STRUCT_INIT_PARAM_LIST);
struct AstExprStructInitParamSpan {
    AstExprStructInitParam * data;
    usize size;
} typedef AstExprStructInitParamSpan;
static AstExprStructInitParamSpan ast_expr_struct_init_param_list_to_span(
    const AstExprStructInitParamList list[ref]) {
    return (AstExprStructInitParamSpan){
        .data = list->data,
        .size = list->size,
    };
}

struct AstExprStructInit {
    SrcSpan span;
    Path path;
    AstExprStructInitParamSpan args;
} typedef AstExprStructInit;

struct AstExpr {
    AstExprType type;
    SrcSpan span;
    union {
        const struct AstFunction * function;
        Path path;
        struct {
            const struct AstExpr * function;
            AstExprSpan args;
        } funcall;
        struct {
            const struct AstExpr * next;
            AstExprUnaryType type;
        } unary;
        struct {
            const struct AstExpr * a;
            const struct AstExpr * b;
            AstExprBinaryType type;
        } binary;
        struct {
            const struct AstExpr * next;
            AstType type;
        } as;
        struct {
            usize value;
        } integer;
        struct {
            const struct AstExpr * next;
            Path name;
        } field_access;
        AstExprStructInit struct_init;
    } as;
} typedef AstExpr;

#define AST_STMT_LIST_TEMPLATE(m) m(AstStmtList, ast_stmt_list, struct AstStmt)
DARRAY_HEADER(AST_STMT_LIST_TEMPLATE);

struct AstStmtSpan {
    const struct AstStmt * data;
    usize size;
} typedef AstStmtSpan;

static AstStmtSpan ast_stmt_list_to_span(const AstStmtList list[ref]) {
    return (AstStmtSpan){
        .data = list->data,
        .size = list->size,
    };
}

enum AstStmtType : u8 {
    AST_STMT_POISONED,
    AST_STMT_RETURN,
    AST_STMT_BLOCK,
    AST_STMT_DECL,
    AST_STMT_EXPR,
    AST_STMT_ASSIGNMENT,
    AST_STMT_STRUCT,
} typedef AstStmtType;

struct AstStmt {
    AstStmtType type;
    SrcSpan span;
    union {
        const struct AstDecl * decl;
        const struct AstStruct * struc;
        struct {
            AstExpr expr;
            bool has_expr;
        } ret;
        AstStmtSpan block;
        AstExpr expr;
        struct {
            AstExpr to;
            AstExpr from;
        } assign;
    } as;
} typedef AstStmt;

struct AstParam {
    SrcSpan span;
    Str iden; // no iden represented by empty string
    AstType type;
} typedef AstParam;

#define AST_PARAM_LIST_TEMPLATE(m) m(AstParamList, ast_param_list, AstParam)
DARRAY_HEADER(AST_PARAM_LIST_TEMPLATE);

struct AstParamSpan {
    const AstParam * data;
    usize size;
} typedef AstParamSpan;

static AstParamSpan ast_param_list_to_span(const AstParamList list[ref]) {
    return (AstParamSpan){
        .data = list->data,
        .size = list->size,
    };
}

struct AstFunction {
    SrcSpan span;
    AstParamSpan params;
    bool has_return_type;
    AstType return_type;
    AstStmtSpan body;
} typedef AstFunction;

struct AstStruct {
    SrcSpan span;
    Str iden;
    AstParamSpan params;
} typedef AstStruct;

struct AstDecl {
    SrcSpan span;
    Str iden;
    bool is_const;
    bool has_type;
    AstType type;
    bool has_expr;
    AstExpr expr;
} typedef AstDecl;

#define AST_TOP_LVL_STMT_LIST_TEMPLATE(m)                                      \
    m(AstTLSList, ast_tls_list, struct AstTopLvlStmt)
DARRAY_HEADER(AST_TOP_LVL_STMT_LIST_TEMPLATE);

struct AstTLSSpan {
    const struct AstTopLvlStmt * data;
    usize size;
} typedef AstTLSSpan;

static AstTLSSpan ast_tls_list_to_span(const AstTLSList list[ref]) {
    return (AstTLSSpan){
        .data = list->data,
        .size = list->size,
    };
}

struct AstModule {
    SrcSpan span;
    Str iden;
    AstTLSSpan body;
} typedef AstModule;

struct AstTopLvlStmt {
    AstTLSType type;
    SrcSpan span;
    union {
        AstModule mod;
        AstDecl decl;
        AstStruct struc;
    } as;
} typedef AstTopLvlStmt;

struct Ast {
    // to be nonnull at the end of parsing
    AstTLSSpan body;
} typedef Ast;

struct ParseError {
    Token unexpected_token;
} typedef ParseError;

enum IrrecoverableParseError : u8 {
    IRRECOVERABLE_PARSE_ERROR_OOM,
    IRRECOVERABLE_PARSE_ERROR_LIMIT_REACHED,
} typedef IrrecoverableParseError;

#define AST_ERROR_LIST_TEMPLATE(m)                                             \
    m(ParseErrorList, parse_error_list, ParseError)
DARRAY_HEADER(AST_ERROR_LIST_TEMPLATE);

struct ParseResult {
    bool irrecoverable;
    union {
        Ast ast;
        IrrecoverableParseError irrecoverable_error;
    };
    ParseErrorList errors;
} typedef ParseResult;

/* This number happens to be a capacity
    of the currently used scaling factor
    for dynamic arrays.
*/
#define MAX_TRANSLATION_UNIT_PARSE_ERRORS 254

struct Parser {
    Str src;
    TokenSpan span;
    usize index;
    ParseErrorList errors;
    jmp_buf catch_site;
    Allocator allocator;
    IrrecoverableParseError caught_error_buff;
} typedef Parser;

/* will not free allocations on failure!
    use with virtual memory arena, buffer allocator, ect...
*/
ParseResult parse(Allocator allocator, Str src, TokenSpan tokens);
