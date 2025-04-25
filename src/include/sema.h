#pragma once

#include "allocator.h"
#include "ast.h"
#include "common.h"
#include "generic/darray.h"
#include <assert.h>
#include <setjmp.h>

enum SymbolType {
    SYMBOL_POISONED,
    SYMBOL_INCOMPLETE_TYPE,
    SYMBOL_INCOMPLETE_DECL,
    SYMBOL_MOD,
    SYMBOL_CNST,
    SYMBOL_VAR,
    SYMBOL_TYPE,
} typedef SymbolType;

struct Cnst {
} typedef Cnst;

struct Var {
} typedef Var;

enum BuiltinType {
    BUILTIN_VOID,
    BUILTIN_U8,
    BUILTIN_U16,
    BUILTIN_U32,
    BUILTIN_U64,
    BUILTIN_I8,
    BUILTIN_16,
    BUILTIN_I32,
    BUILTIN_I64,
} typedef BuiltinType;

enum TypeType {
    TYPE_POINTER,
    TYPE_REFERENCE,
    TYPE_FN,
    TYPE_BUILTIN,
    TYPE_DISTINCT_ALIAS,
} typedef TypeType;

#define TYPE_LIST_TEMPLATE(m) m(TypeList, type_list, const struct Type *)
DARRAY_HEADER(TYPE_LIST_TEMPLATE);

struct TypeSpan {
    const struct Type ** data;
    usize size;
} typedef TypeSpan;
static TypeSpan type_list_to_span(const TypeList list[ref]) {
    return (TypeSpan){
        .data = list->data,
        .size = list->size,
    };
}

struct Type {
    TypeType type;
    union {
        const struct Type * pointer;
        const struct Type * reference;
        const struct Type * distinct_alias;
        struct {
            const struct Type * return_type;
            TypeSpan parameters;
        } function;
        BuiltinType builtin;
    } as;
} typedef Type;

struct Symbol {
    Str iden;
    SymbolType type;
    SrcSpan span;
    bool reachable : 1;
    bool visited : 1;
    union {
        const AstType * incomplete_type;
        const AstDecl * incomplete_decl;
        struct Module * module;
        Cnst * cnst;
        Var * var;
        const Type * type;
    } as;
} typedef Symbol;

#define SYMBOL_LIST_TEMPLATE(m) m(SymbolList, symbol_list, Symbol)
DARRAY_HEADER(SYMBOL_LIST_TEMPLATE);
struct SymbolSpan {
    Symbol * data;
    usize size;
} typedef SymbolSpan;
static SymbolSpan symbol_list_to_span(SymbolList list[ref]) {
    return (SymbolSpan){
        .data = list->data,
        .size = list->size,
    };
}
#define MODULE_ID_VALID(id) ((id) > 0)
struct Module {
    struct Module * parent;
    SymbolSpan body;
} typedef Module;
#define MODULE_LIST(m) m(ModuleList, module_list, Module)
DARRAY_HEADER(MODULE_LIST);

struct SymbolTable {
    Str project_name;
    ModuleList list;
} typedef SymbolTable;

enum SemaException {
    SEMA_EXCEPT_OOM,
} typedef SemaException;
enum SemaErrorType {
    SEMA_ERROR_DUPLICATE,
    SEMA_ERROR_UNEXPECTED_IDENTIFIER,
} typedef SemaErrorType;
struct SemaError {
    SemaErrorType type;
    SrcSpan span;
    union {
        struct {
            SrcSpan orig_span;
            Module * parent;
            Str iden;
        } duplicate;
        Path unexpected_ident;
    } as;
} typedef SemaError;
#define SEMA_ERROR_LIST_TEMPLATE(m) m(SemaErrorList, sema_error_list, SemaError)
DARRAY_HEADER(SEMA_ERROR_LIST_TEMPLATE);
struct SemaCtx {
    Allocator allocator;
    SemaErrorList errors;
    jmp_buf catch_site;
    SemaException exception;
} typedef SemaCtx;
struct SemaLoc {
    SymbolTable * root;
    Module * module;
} typedef SemaLoc;
// PRECONDITION: parameter modules address must be stable
// for the lifetime of the child symbols
void tls_span_to_module_decl(
    SemaCtx ctx[ref], Module parent[ref], AstTLSSpan span, Module module[ref]
);
void symbol_table_implement(SemaCtx ctx[ref], SymbolTable table[ref]);
extern const SymbolSpan BUILTIN_SYMBOLS;
const Type * builtin_void();
