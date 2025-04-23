#pragma once

#include "allocator.h"
#include "ast.h"
#include "common.h"
#include "generic/darray.h"
#include "str.h"
#include <setjmp.h>

typedef struct SymbolTable Module;

struct Type {
} typedef Type;

struct VarDeclData {
    bool has_type;
    Type type;
} typedef VarDeclData;

#define SYMBOL_TABLE_ENTRY_LIST_TEMPLATE(m)                                    \
    m(SymbolTableEntryList, symbol_table_entry_list, struct SymbolTableEntry)
DARRAY_HEADER(SYMBOL_TABLE_ENTRY_LIST_TEMPLATE);

struct SymbolTable {
    SymbolTableEntryList list;
} typedef SymbolTable;

enum SymbolTableEntryType {
    SYMBOL_TABLE_ENTRY_POISONED,
    SYMBOL_TABLE_ENTRY_MOD,
    SYMBOL_TABLE_ENTRY_VAR,
} typedef SymbolTableEntryType;

struct SymbolTableEntry {
    Str name;
    SrcSpan span;
    SymbolTableEntryType type;
    union {
        Module module;
    } as;
} typedef SymbolTableEntry;

enum SemaErrorType {
    SEMA_ERROR_REDEFINED_SYMBOL,
} typedef SemaErrorType;

struct SemaError {
    SemaErrorType type;
    union {
        struct {
            Str symbol;
            SrcSpan first;
            SrcSpan second;
        } redefined_symbol;
    } as;
} typedef SemaError;

#define SEMA_ERROR_LIST_TEMPLATE(m) m(SemaErrorList, sema_error_list, SemaError)
DARRAY_HEADER(SEMA_ERROR_LIST_TEMPLATE);

struct SemaErrorSpan {
    const SemaError * data;
    usize size;
} typedef SemaErrorSpan;

enum IrrecoverableSemaError {
    SEMA_IRRECOVERABLE_ERROR_OOM,
} typedef IrrecoverableSemaError;

static SemaErrorSpan sema_error_list_to_span(const SemaErrorList list[ref]) {
    return (SemaErrorSpan){
        .data = list->data,
        .size = list->size,
    };
}

struct SemaResult {
    bool irrecoverable;
    SemaErrorSpan errors;
    union {
        SymbolTable table;
        IrrecoverableSemaError irrecoverable_error;
    };
} typedef SemaResult;

struct SemaCtx {
    SemaErrorList errors;
    Allocator allocator;
    jmp_buf catch_site;
    IrrecoverableSemaError caught_error_buff;
} typedef SemaCtx;

SemaResult semantic_analyze(Ast ast);
