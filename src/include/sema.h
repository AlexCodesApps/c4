#pragma once

#include "allocator.h"
#include "ast.h"
#include "common.h"
#include "generic/darray.h"
#include "str.h"
#include "utility.h"
#include <setjmp.h>

struct StructField {
    usize offset;
    Str name;
    struct Type * type;
} typedef StructField;

#define STRUCT_FIELD_LIST(m) m(StructFieldList, struct_field_list, StructField)
DARRAY_HEADER(STRUCT_FIELD_LIST);

struct Struct {
    usize size;
    usize align;
    StructFieldList fields;
} typedef Struct;

enum TypeType {
    TYPE_BUILTIN = 0b00,
    TYPE_POINTER = 0b01,
    TYPE_REFERENCE = 0b10,
    TYPE_STRUCT = 0b11,
    TYPE_INCOMPLETE_STRUCT = 0b100,
} typedef TypeType;

struct Type {
    usize recursive_marker; // used in detecting circular type definitions
    TypeType type;
    union {
        struct Type * pointer;
        struct Type * reference;
        Struct struc;
        const AstStruct * incomplete_struc;

    } as;
} typedef Type;

bool type_is_complete(Type * type);

struct Cnst {
} typedef Cnst;
struct Expr {
} typedef Expr;

struct Decl {
    bool is_complete;
    union {
        struct {
            bool is_const;
            Type * sema_type;
            Expr expr;
        };
        const AstDecl * incomplete;
    };
} typedef Decl;

enum SymbolType {
    SYMBOL_TYPE = 0b000,
    SYMBOL_DECL = 0b001,
    SYMBOL_MOD = 0b010,
    SYMBOL_INCOMPLETE_TYPE = 0x100,
    SYMBOL_INCOMPLETE_DECL = 0x101,
    SYMBOL_INCOMPLETE_MOD = 0x110,
} typedef SymbolType;

struct Symbol {
    SrcSpan span;
    Str iden;
    SymbolType sym_type;
    union {
        Type * type;
        Decl * decl;
        struct Module * module;
        const AstType * incomplete_type;
        const AstDecl * incomplete_decl;
    } as;
} typedef Symbol;

bool symbol_well_defined(const Symbol sym[ref]);

#define SYMBOL_LIST_TEMPLATE(m) m(SymbolList, symbol_list, struct Symbol *)
DARRAY_HEADER(SYMBOL_LIST_TEMPLATE);

struct Module {
    SymbolList list;
} typedef Module;
struct SymbolTable {
    SymbolList list;
} typedef SymbolTable;

enum SemaErrorType { SEMA_ERROR_REDEFINED } typedef SemaErrorType;
struct SemaError {
    SemaErrorType type;
    struct {
        struct {
            Module * mod;
            Str iden;
            SrcSpan a;
            SrcSpan b;
        } redefined;
    } as;
} typedef SemaError;

#define SEMA_ERROR_LIST_TEMPLATE(m) m(SemaErrorList, sema_error_list, SemaError)
DARRAY_HEADER(SEMA_ERROR_LIST_TEMPLATE);

enum SemaException { SEMA_EXCEPT_OOM } typedef SemaException;

struct SemaCtx {
    Allocator allocator;
    jmp_buf catch_site;
    SemaErrorList errors;
    SemaException exception;
} typedef SemaCtx;

void sema_declare_module(SemaCtx * ctx, const AstModule * in, Module * out);
void sema_complete_module(SemaCtx * ctx, Module * module);

bool sema_complete_type(SemaCtx * ctx, Type * type);
bool sema_complete_decl(SemaCtx * ctx, Decl * type);

bool sema_type_equal(const Type a[ref], const Type b[ref]);
