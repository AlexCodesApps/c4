#include "include/sema.h"
#include "include/ast.h"
#include "include/generic/darray.h"
#include "include/utility.h"
#include <setjmp.h>

DARRAY_IMPL(SYMBOL_TABLE_ENTRY_LIST_TEMPLATE);
DARRAY_IMPL(SEMA_ERROR_LIST_TEMPLATE);

static void throw(SemaCtx ctx[ref], IrrecoverableSemaError err) {
    ctx->caught_error_buff = err;
    longjmp(ctx->catch_site, 1);
}

static void emit_error(SemaCtx ctx[ref], SemaError error) {
    if (!sema_error_list_push(&ctx->errors, error)) {
        throw(ctx, SEMA_IRRECOVERABLE_ERROR_OOM);
    }
}

static Module
semantic_analyze_module(SemaCtx ctx[ref], const AstModule mod[ref]) {
    SymbolTable table = {.list = symbol_table_entry_list_new(ctx->allocator)};
    foreach_span(&mod->body, tls) {
        switch (tls->type) {
        case AST_TLS_TYPE_POISONED:
            continue;
        case AST_TLS_TYPE_MOD: {
            foreach_span(&table.list, entry) {
                if (str_eq(entry->name, tls->mod.iden)) {
                    emit_error(
                        ctx, (SemaError){.type = SEMA_ERROR_REDEFINED_SYMBOL,
                                         .as.redefined_symbol =
                                             {.symbol = entry->name,
                                              .first = entry->span,
                                              .second = tls->span}}
                    );
                    continue;
                }
            }
            Module sema_mod = semantic_analyze_module(ctx, &tls->mod);
            SymbolTableEntry entry = {
                .name = mod->iden,
                .span = tls->span,
                .type = SYMBOL_TABLE_ENTRY_MOD,
                .as.module = sema_mod,
            };
            if (!symbol_table_entry_list_push(&table.list, entry)) {
                throw(ctx, SEMA_IRRECOVERABLE_ERROR_OOM);
            }
        } break;
        case AST_TLS_TYPE_DECL:
        }
    }
    return table;
}

SemaResult semantic_analyze(Ast ast) {
    foreach_span(&ast.body, tls) {}
}
