#include "include/sema.h"
#include "include/ast.h"
#include "include/common.h"
#include "include/generic/darray.h"
#include "include/str.h"
#include "include/utility.h"
#include <setjmp.h>

DARRAY_IMPL(TYPE_LIST_TEMPLATE);
DARRAY_IMPL(SYMBOL_LIST_TEMPLATE);
DARRAY_IMPL(SEMA_ERROR_LIST_TEMPLATE);

#define OOM_CHECK(b)                                                           \
    if (!(b)) {                                                                \
        throw(ctx, SEMA_EXCEPT_OOM);                                           \
    }
#define LIFT(...)                                                              \
    ({                                                                         \
        typeof_unqual(__VA_ARGS__) * alloc = allocator_alloc_uninit(           \
            (ctx)->allocator, typeof_unqual(__VA_ARGS__)                       \
        );                                                                     \
        OOM_CHECK(alloc);                                                      \
        *alloc = (__VA_ARGS__);                                                \
        alloc;                                                                 \
    })

static bool symbol_table_implement_symbol(
    SemaCtx ctx[ref], Module module[ref], Symbol sym[ref]
);

static void throw(SemaCtx ctx[ref], SemaException except) {
    ctx->exception = except;
    longjmp(ctx->catch_site, 1);
}

static void emit_error(SemaCtx ctx[ref], SemaError error) {
    OOM_CHECK(sema_error_list_push(&ctx->errors, error));
}

static Symbol * symbol_span_has_mod_with_iden(SymbolSpan span, Str iden) {
    foreach_span(&span, sym) {
        if (sym->type == SYMBOL_MOD && str_eq(sym->iden, iden)) {
            return sym;
        }
    }
    return nullptr;
}

static Symbol * symbol_span_has_decl_with_iden(SymbolSpan span, Str iden) {
    foreach_span(&span, sym) {
        switch (sym->type) {
        case SYMBOL_VAR:
        case SYMBOL_CNST:
        case SYMBOL_INCOMPLETE_DECL:
            if (str_eq(sym->iden, iden)) {
                return sym;
            }
            break;
        default:
        }
    }
    return nullptr;
}

void tls_span_to_module_decl(
    SemaCtx ctx[ref], Module parent[ref], AstTLSSpan span, Module module[ref]
) {
    module->parent = parent;
    SymbolList list = symbol_list_new(ctx->allocator);
    foreach_span(&span, tls) {
        switch (tls->type) {
        case AST_TLS_TYPE_POISONED:
            continue;
        case AST_TLS_TYPE_DECL: {
            Symbol * dup = symbol_span_has_decl_with_iden(
                symbol_list_to_span(&list), tls->decl.iden
            );
            if (dup) {
                emit_error(
                    ctx, (SemaError){.type = SEMA_ERROR_DUPLICATE,
                                     .as.duplicate =
                                         {
                                             .iden = tls->decl.iden,
                                             .orig_span = dup->span,
                                             .parent = module,
                                         }}
                );
                continue;
            }
        }
            Symbol decl = {
                .iden = tls->decl.iden,
                .type = SYMBOL_INCOMPLETE_DECL,
                .span = tls->span,
                .reachable = false,
                .visited = false,
                .as.incomplete_decl = &tls->decl,
            };
            OOM_CHECK(symbol_list_push(&list, decl));
            break;
        case AST_TLS_TYPE_MOD: {
            Symbol * dup = symbol_span_has_mod_with_iden(
                symbol_list_to_span(&list), tls->mod.iden
            );
            if (dup) {
                emit_error(
                    ctx, (SemaError){.type = SEMA_ERROR_DUPLICATE,
                                     .as.duplicate =
                                         {
                                             .iden = tls->decl.iden,
                                             .orig_span = dup->span,
                                             .parent = module,
                                         }}
                );
                continue;
            }
        }
            Module * child_mod = allocator_alloc(ctx->allocator, Module);
            OOM_CHECK(child_mod);
            tls_span_to_module_decl(ctx, module, tls->mod.body, child_mod);
            child_mod->parent = module;
            Symbol mod_sym = {
                .iden = tls->mod.iden,
                .type = SYMBOL_MOD,
                .span = tls->span,
                .reachable = false,
                .visited = false,
                .as.module = child_mod,
            };
            OOM_CHECK(symbol_list_push(&list, mod_sym));
            break;
        }
    }
    module->body = symbol_list_to_span(&list);
}

static const Type * builtin_table_lookup_type(Str name) {
    foreach_span(&BUILTIN_SYMBOLS, sym) {
        if (sym->type == SYMBOL_TYPE && str_eq(sym->iden, name)) {
            return sym->as.type;
        }
    }
    return nullptr;
}

static const Type *
symbol_table_lookup_type(SemaCtx ctx[ref], Module module[ref], Path path) {
    usize index = 0;
    for (;;) {
        Str cur = *span_at(&path.list, index);
        if (index == path.list.size - 1) {
            foreach_span(&module->body, sym) {
                if (sym->type == SYMBOL_TYPE && str_eq(sym->iden, cur)) {
                    return sym->as.type;
                }
            }
        } else {
            foreach_span(&module->body, sym) {
                if (sym->type == SYMBOL_MOD && str_eq(sym->iden, cur)) {
                    module = sym->as.module;
                    ++index;
                    continue;
                }
            }
        }
        if (!module->parent) {
            if (++index < path.list.size) {
                return nullptr;
            }
            return builtin_table_lookup_type(cur);
        }
        module = module->parent;
    }
}
// null on invalid symbol
static const Type * symbol_table_type_from_ast(
    SemaCtx ctx[ref], Module * module, const AstType type[ref]
) {
    switch (type->type) {
    case AST_TYPE_POISONED:
        return nullptr;
    case AST_TYPE_POINTER:
        const Type * ntype =
            symbol_table_type_from_ast(ctx, module, type->as.pointer);
        if (!ntype) {
            return nullptr;
        }
        return LIFT((Type){.type = TYPE_POINTER, .as.pointer = ntype});
    case AST_TYPE_REFERENCE:
        ntype = symbol_table_type_from_ast(ctx, module, type->as.reference);
        if (!ntype) {
            return nullptr;
        }
        return LIFT((Type){.type = TYPE_REFERENCE, .as.reference = ntype});
    case AST_TYPE_FN:
        if (type->as.function.has_return_type) {
            ntype = symbol_table_type_from_ast(
                ctx, module, type->as.function.return_type
            );
        } else {
            ntype = builtin_void();
        }
        TypeList parameters;
        foreach_span(&type->as.function.parameters, param) {
            const Type * param_t =
                symbol_table_type_from_ast(ctx, module, param);
            if (!param_t) {
                return nullptr;
            }
            OOM_CHECK(type_list_push(&parameters, param_t));
        }
        return LIFT((Type){.type = TYPE_FN,
                           .as.function = {
                               .return_type = ntype,
                               .parameters = type_list_to_span(&parameters),
                           }});
    case AST_TYPE_PATH:
        ntype = symbol_table_lookup_type(ctx, module, type->as.path);
        if (!ntype) {
            emit_error(
                ctx,
                (SemaError){
                    .type = SEMA_ERROR_UNEXPECTED_IDENTIFIER,
                    .span = type->span,
                    .as.unexpected_ident = type->as.path,
                }
            );
        }
        return ntype;
    }
}

static bool
sema_analyze_cnst(SemaCtx ctx[ref], const AstExpr expr[ref], Cnst out[ref]) {
    Cnst cnst;
    switch (expr->type) {
    case AST_EXPR_UNARY:
        auto * unary = &expr->as.unary;
        if (!sema_analyze_cnst(ctx, expr, &cnst)) {
            return false;
        }
        TODO;
    }
}

static bool
decl_to_symbol(SemaCtx ctx[ref], Symbol sym[ref], const AstDecl decl[ref]) {
    TODO;
}

// false indicates potential circular dependancy
static bool symbol_table_implement_symbol(
    SemaCtx ctx[ref], Module module[ref], Symbol sym[ref]
) {
    if (sym->visited) {
        return false;
    }
    sym->visited = true;
    switch (sym->type) {
    case SYMBOL_POISONED:
    case SYMBOL_TYPE:
    case SYMBOL_VAR:
    case SYMBOL_CNST:
        break;
    case SYMBOL_MOD:
        foreach_span(&sym->as.module->body, sym2) {
            symbol_table_implement_symbol(ctx, module, sym2);
        }
        break;
    case SYMBOL_INCOMPLETE_TYPE:
        const Type * ntype =
            symbol_table_type_from_ast(ctx, module, sym->as.incomplete_type);
        if (!ntype) {
            sym->type = SYMBOL_POISONED;
            break;
        }
        sym->type = SYMBOL_TYPE;
        sym->as.type = ntype;
        break;
    case SYMBOL_INCOMPLETE_DECL:
        if (!decl_to_symbol(ctx, sym, sym->as.incomplete_decl)) {
            sym->type = SYMBOL_POISONED;
        }
        break;
    }
    return true;
}

void symbol_table_implement(SemaCtx ctx[ref], SymbolTable table[ref]) {}

enum {
    BUILTIN_VOID_INDEX,
    BUILTIN_U8_INDEX,
    BUILTIN_U16_INDEX,
    BUILTIN_U32_INDEX,
    BUILTIN_U64_INDEX,
    BUILTIN_I8_INDEX,
    BUILTIN_I16_INDEX,
    BUILTIN_I32_INDEX,
    BUILTIN_I64_INDEX,
    BUILTIN_BOOL_INDEX,
};

const Type builtin_types[] = {
    [BUILTIN_VOID_INDEX] =
        {
            .type = TYPE_BUILTIN,
            .as.builtin = BUILTIN_VOID,
        },
    [BUILTIN_U8_INDEX] =
        {
            .type = TYPE_BUILTIN,
            .as.builtin = BUILTIN_U8,
        },
    [BUILTIN_U16_INDEX] =
        {
            .type = TYPE_BUILTIN,
            .as.builtin = BUILTIN_U16,
        },
    [BUILTIN_U32_INDEX] =
        {
            .type = TYPE_BUILTIN,
            .as.builtin = BUILTIN_U32,
        },
    [BUILTIN_U64_INDEX] =
        {
            .type = TYPE_BUILTIN,
            .as.builtin = BUILTIN_U64,
        },
    [BUILTIN_I8_INDEX] =
        {
            .type = TYPE_BUILTIN,
            .as.builtin = BUILTIN_I8,
        },
    [BUILTIN_I32_INDEX] =
        {
            .type = TYPE_BUILTIN,
            .as.builtin = BUILTIN_I32,
        },
    [BUILTIN_I64_INDEX] =
        {
            .type = TYPE_BUILTIN,
            .as.builtin = BUILTIN_I64,
        },
    [BUILTIN_BOOL_INDEX] = {
        .type = TYPE_DISTINCT_ALIAS,
        .as.distinct_alias = &builtin_types[BUILTIN_U8_INDEX]
    },
};

#define BUILTIN_INDEX_TYPE(index, name)                                        \
    [index] = {                                                                \
        .iden = s(#name),                                                      \
        .type = SYMBOL_TYPE,                                                   \
        .span = {},                                                            \
        .reachable = true,                                                     \
        .visited = true,                                                       \
        .as.type = &builtin_types[index],                                      \
    }

Symbol builtin_symbols_array[] = {
    BUILTIN_INDEX_TYPE(BUILTIN_VOID_INDEX, void),
    BUILTIN_INDEX_TYPE(BUILTIN_I8_INDEX, i8),
    BUILTIN_INDEX_TYPE(BUILTIN_I16_INDEX, i16),
    BUILTIN_INDEX_TYPE(BUILTIN_I32_INDEX, i32),
    BUILTIN_INDEX_TYPE(BUILTIN_I64_INDEX, i64),
    BUILTIN_INDEX_TYPE(BUILTIN_U8_INDEX, u8),
    BUILTIN_INDEX_TYPE(BUILTIN_U16_INDEX, u16),
    BUILTIN_INDEX_TYPE(BUILTIN_U32_INDEX, u32),
    BUILTIN_INDEX_TYPE(BUILTIN_U64_INDEX, u64),
    BUILTIN_INDEX_TYPE(BUILTIN_BOOL_INDEX, bool),
};

const Type * builtin_void() { return &builtin_types[BUILTIN_VOID_INDEX]; }

const SymbolSpan BUILTIN_SYMBOLS = {
    .data = builtin_symbols_array,
    .size = ARRAY_SIZE(builtin_symbols_array),
};
