#pragma once

#include "allocator.h"
#include "common.h"
#include "generic/darray.h"
#include "lexer.h"
#include "str.h"

enum AstTLSType {
    AST_TLS_TYPE_DECL,
    AST_TLS_TYPE_MOD,
    AST_TLS_TYPE_POISONED,
} typedef AstTLSType;

#define AST_PATH_TEMPLATE(m) \
    m(AstPathList, ast_path_list, Str)
DARRAY_HEADER(AST_PATH_TEMPLATE);
struct AstPath {
    SrcSpan span;
    bool is_global;
    AstPathList list;
} typedef AstPath;

#define AST_TYPE_LIST_TEMPLATE(m) \
    m(AstTypeList, ast_type_list, struct AstType)
DARRAY_HEADER(AST_TYPE_LIST_TEMPLATE);

enum AstTypeType : u8 {
    AST_TYPE_POISONED,
    AST_TYPE_POINTER,
    AST_TYPE_REFERENCE,
    AST_TYPE_FN,
    AST_TYPE_PATH,
} typedef AstTypeType;

struct AstType {
    AstTypeType type;
    SrcSpan span;
    union {
        struct AstType * next;
        AstPath path;
        struct {
            bool has_return_type;
            struct AstType * return_type;
            AstTypeList parameters;
        } function;
    };
} typedef AstType;

#define AST_EXPR_LIST_TEMPLATE(m) \
    m(AstExprList, ast_expr_list, struct AstExpr)
DARRAY_HEADER(AST_EXPR_LIST_TEMPLATE);

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
} typedef AstExprType;

struct AstExpr {
    AstExprType type;
    SrcSpan span;
    union {
        struct AstFunction * function;
        struct AstPath path;
        struct {
            struct AstExpr * function;
            AstExprList args;
        } funcall;
        struct {
            struct AstExpr * next;
            AstExprUnaryType type;
        } unary;
        struct {
            struct AstExpr * a;
            struct AstExpr * b;
            AstExprBinaryType type;
        } binary;
        struct {
            struct AstExpr * next;
            AstType type;
        } as;
        struct  {
            usize value;
        } integer;
        struct {
            struct AstExpr * next;
            AstPath name;
        } field_access;
    };
} typedef AstExpr;

#define AST_STMT_LIST_TEMPLATE(m) \
    m(AstStmtList, ast_stmt_list, struct AstStmt)
DARRAY_HEADER(AST_STMT_LIST_TEMPLATE);

enum AstStmtType : u8 {
    AST_STMT_RETURN,
    AST_STMT_POISONED,
    AST_STMT_BLOCK,
    AST_STMT_DECL,
    AST_STMT_EXPR,
    AST_STMT_ASSIGNMENT,
} typedef AstStmtType;

struct AstStmt {
    AstStmtType type;
    SrcSpan span;
    union {
        struct AstDecl * decl;
        struct {
            AstExpr return_expr;
            bool has_return_expr;
        };
        AstStmtList block;
        AstExpr expr;
        struct {
            AstExpr to;
            AstExpr from;
        } assign;
    };
} typedef AstStmt;

struct AstFunParam {
    SrcSpan span;
    Str iden; // no iden represented by empty string
    AstType type;
} typedef AstFunParam;

#define AST_FUN_PARAM_LIST_TEMPLATE(m) \
    m(AstFunParamList, ast_fun_param_list, AstFunParam)
DARRAY_HEADER(AST_FUN_PARAM_LIST_TEMPLATE);

struct AstFunction {
    SrcSpan span;
    AstFunParamList params;
    bool has_return_type;
    AstType return_type;
    AstStmtList body;
} typedef AstFunction;

struct AstDecl {
    SrcSpan span;
    Str iden;
    bool is_const;
    bool has_type;
    AstType type;
    bool has_expr;
    AstExpr expr;
} typedef AstDecl;

#define AST_TOP_LVL_STMT_LIST_TEMPLATE(m) \
    m(AstTLSList, ast_tls_list, const struct AstTopLvlStmt *)
DARRAY_HEADER(AST_TOP_LVL_STMT_LIST_TEMPLATE);

struct AstModule {
    SrcSpan span;
    Str iden;
    AstTLSList body;
} typedef AstModule;

struct AstTopLvlStmt {
    AstTLSType type;
    SrcSpan span;
    union {
        AstModule mod;
        AstDecl decl;
    };
} typedef AstTopLvlStmt;


struct Ast {
    // to be nonnull at the end of parsing
    AstTLSList list;
} typedef Ast;

struct ParseError {
    Token unexpected_token;
} typedef ParseError;

enum IrrecoverableParseError : u8 {
    IRRECOVERABLE_PARSE_ERROR_OOM,
    IRRECOVERABLE_PARSE_ERROR_LIMIT_REACHED,
} typedef IrrecoverableParseError;

#define AST_ERROR_LIST_TEMPLATE(m) \
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
