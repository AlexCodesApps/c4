#pragma once

#include "str.h"
#include "utility.h"
struct Type {
} typedef Type;
struct Decl {
    bool is_const;
};

enum SymbolType {
    SYMBOL_TYPE,
    SYMBOL_DECL,
    SYMBOL_MOD,
} typedef SymbolType;

struct Symbol {
    Str identifier;
    Type * sema_type;       // never null on well defined symbol
    usize recursive_marker; // used in detecting circular type definitions
    SymbolType sym_type;
    struct {
        Type * type;
    } as;
} typedef Symbol;

bool symbol_well_defined(const Symbol sym[ref]);

struct SymbolTable {

} typedef SymbolTable;
