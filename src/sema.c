#include "include/sema.h"
#include "include/assert.h" // IWYU pragma: keep
#include "include/ast.h"
#include "include/generic/darray.h"
#include "include/str.h"
#include "include/utility.h"
#include <setjmp.h>
DARRAY_IMPL(SEMA_ERROR_LIST_TEMPLATE);
DARRAY_IMPL(SYMBOL_LIST_TEMPLATE);

[[noreturn]] static void throw(SemaCtx * ctx, SemaException exception) {
    ctx->exception = exception;
    longjmp(ctx->catch_site, 1);
}

static void emit_error(SemaCtx * ctx, SemaError error) {
    if (!sema_error_list_push(&ctx->errors, error)) {
        throw(ctx, SEMA_EXCEPT_OOM);
    }
}

#define ALLOCATE(ctx, ...)                                                     \
    ({                                                                         \
        auto ptr = allocator_alloc_uninit((ctx)->allocator,                    \
                                          typeof_unqual(__VA_ARGS__));         \
        if (!ptr) {                                                            \
            throw((ctx), SEMA_EXCEPT_OOM);                                     \
        }                                                                      \
        *ptr = (__VA_ARGS__);                                                  \
        ptr;                                                                   \
    })
#define ALLOCATE_TYPE(ctx, type)                                               \
    ({                                                                         \
        auto ptr = allocator_alloc_uninit((ctx)->allocator, type);             \
        if (!ptr) {                                                            \
            throw((ctx), SEMA_EXCEPT_OOM);                                     \
        }                                                                      \
        ptr;                                                                   \
    })

bool symbol_well_defined(const Symbol sym[ref]) {
    return (sym->sym_type & 0b100) == 0;
}

bool type_is_complete(Type * type) { return (type->type & 0b100) == 0; }

static int symbol_type_strip_incomplete_flag(SymbolType type) {
    return type & 0b11;
}

void sema_declare_module(SemaCtx * ctx, const AstModule * in, Module * out) {
    Str iden;
    Symbol * sym;
    Module * module;
    Decl * decl;
    Type * type;
    out->list = symbol_list_new(ctx->allocator);
    foreach_span(&in->body, tls) {
        switch (tls->type) {
        case AST_TLS_POISONED:
            break;
        case AST_TLS_MOD:
            iden = tls->as.mod.iden;
            if (!str_eq(iden, s("_"))) {
                foreach_span(&out->list, _sym) {
                    Symbol * sym = *_sym;
                    if (symbol_type_strip_incomplete_flag(sym->sym_type) ==
                            SYMBOL_MOD &&
                        str_eq(sym->iden, iden)) {
                        emit_error(ctx,
                                   (SemaError){.type = SEMA_ERROR_REDEFINED,
                                               .as.redefined = {
                                                   .iden = iden,
                                                   .mod = out,
                                                   .a = sym->span,
                                                   .b = tls->span,
                                               }});
                        continue;
                    }
                }
            }
            module = ALLOCATE_TYPE(ctx, Module);
            sema_declare_module(ctx, &tls->as.mod, module);
            sym = ALLOCATE(ctx, (Symbol){
                                    .span = tls->span,
                                    .iden = iden,
                                    .sym_type = SYMBOL_MOD,
                                    .as.module = module,
                                });
            if (!symbol_list_push(&out->list, sym)) {
                throw(ctx, SEMA_EXCEPT_OOM);
            }
            break;
        case AST_TLS_STRUCT:
            iden = tls->as.mod.iden;
            if (!str_eq(iden, s("_"))) {
                foreach_span(&out->list, _sym) {
                    Symbol * sym = *_sym;
                    if (symbol_type_strip_incomplete_flag(sym->sym_type) ==
                            SYMBOL_TYPE &&
                        str_eq(sym->iden, iden)) {
                        emit_error(ctx,
                                   (SemaError){.type = SEMA_ERROR_REDEFINED,
                                               .as.redefined = {
                                                   .iden = iden,
                                                   .mod = out,
                                                   .a = sym->span,
                                                   .b = tls->span,
                                               }});
                        continue;
                    }
                }
            }
            type = ALLOCATE(ctx, (Type){.recursive_marker = 0,
                                        .type = TYPE_STRUCT,
                                        .as.incomplete_struc = &tls->as.struc});
            sym = ALLOCATE(ctx, (Symbol){
                                    .span = tls->span,
                                    .iden = tls->as.struc.iden,
                                    .sym_type = SYMBOL_TYPE,
                                    .as.type = type,
                                });
            if (!symbol_list_push(&out->list, sym)) {
                throw(ctx, SEMA_EXCEPT_OOM);
            }
            break;
        case AST_TLS_DECL:
            iden = tls->as.decl.iden;
            if (!str_eq(iden, s("_"))) {
                foreach_span(&out->list, _sym) {
                    Symbol * sym = *_sym;
                    if (symbol_type_strip_incomplete_flag(sym->sym_type) ==
                            SYMBOL_DECL &&
                        str_eq(sym->iden, iden)) {
                        emit_error(ctx,
                                   (SemaError){.type = SEMA_ERROR_REDEFINED,
                                               .as.redefined = {
                                                   .iden = iden,
                                                   .mod = out,
                                                   .a = sym->span,
                                                   .b = tls->span,
                                               }});
                        continue;
                    }
                }
            }
            decl = ALLOCATE(ctx, (Decl){
                                     .is_complete = false,
                                     .incomplete = &tls->as.decl,
                                 });
            sym = ALLOCATE(ctx, (Symbol){
                                    .span = tls->span,
                                    .iden = tls->as.struc.iden,
                                    .sym_type = SYMBOL_DECL,
                                    .as.decl = decl,
                                });
            if (!symbol_list_push(&out->list, sym)) {
                throw(ctx, SEMA_EXCEPT_OOM);
            }
            break;
        }
    }
}

bool sema_complete_decl(SemaCtx * ctx, Decl * type) {
	TODO;
}

void sema_complete_module(SemaCtx * ctx, Module * module) {
    usize i = 0;
    while (i < module->list.size) {
        Symbol * sym = *span_at(&module->list, i);
        switch (sym->sym_type) {
        case SYMBOL_MOD:
        case SYMBOL_TYPE:
        case SYMBOL_DECL:
            break;
        case SYMBOL_INCOMPLETE_MOD:
            sema_complete_module(ctx, sym->as.module);
            sym->sym_type = SYMBOL_MOD;
            break;
        case SYMBOL_INCOMPLETE_TYPE:
            if (!sema_complete_type(ctx, sym->as.type)) {
                Symbol * rsym;
                ASSERT(symbol_list_pop(&module->list, &rsym));
                *span_at(&module->list, i) = rsym;
                continue;
            }
            sym->sym_type = SYMBOL_TYPE;
            break;
        case SYMBOL_INCOMPLETE_DECL:
            if (!sema_complete_decl(ctx, sym->as.decl)) {
                Symbol * rsym;
                ASSERT(symbol_list_pop(&module->list, &rsym));
                *span_at(&module->list, i) = rsym;
                continue;
            }
            sym->sym_type = SYMBOL_DECL;
            break;
        }
        ++i;
    }
}

bool sema_type_equal(const Type a[ref], const Type b[ref]) {
	TODO;
}

#define TYPE_WORKLIST(m) \
	m(TypeWorklist, type_worklist, Type *)
DARRAY_HEADER(TYPE_WORKLIST);
DARRAY_IMPL(TYPE_WORKLIST);

static bool sema_complete_type_impl(SemaCtx * ctx, Type * type, usize lvl,
		TypeWorklist * list) {
    switch (type->type) {
    case TYPE_POINTER:
    case TYPE_REFERENCE:
		foreach_span(list, otype) { // test type isn't alr queued
			if (otype == type->as.pointer) {
				break;	
			}
		}
		if (!type_worklist_push(list, type->as.pointer)) {
			throw(ctx, SEMA_EXCEPT_OOM); 
		}
    case TYPE_STRUCT:
    case TYPE_BUILTIN:
		break;
    case TYPE_INCOMPLETE_STRUCT:
		bool ret = true;
		if (type->recursive_marker == lvl) {
			TODO; // add suitable error, impossibly sized type detected
		}
		usize saved_lvl = type->recursive_marker;
		type->recursive_marker = lvl;
		foreach_span(&type->as.incomplete_struc->params, param) {
			Type * ptype;
			TODO; // need to implement AstType -> Type lookup op
			if (!sema_complete_type_impl(ctx, ptype, lvl, list)) {
				ret = false;
			}
		}
		type->recursive_marker = saved_lvl;
		return ret;
    }
	return true;
}

bool sema_complete_type(SemaCtx * ctx, Type * type) {
	/*	This algorithm works by recursively defining types with struct definitions
		using a recursive_marker field to check if there is an
		impossible recursive dependancy
		Any a pointer/indirect dependancy is found, the type is put
		on a worklist to be implemented. This avoids an infinite recursion
		with an infinitely recursive type def via pointers/ some direction
		by simply queueing the indirect dependency
	*/
	TypeWorklist worklist = type_worklist_new(ctx->allocator);
	if (!sema_complete_type_impl(ctx, type, 0, &worklist)) {
		return false;
	}
	Type * qtype;
	while (type_worklist_pop(&worklist, &qtype)) {
		if (!sema_complete_type_impl(ctx, qtype, 0, &worklist)) {
			return false; // will edit to allow for showing more errors probs
		}
	}
	return true;
}
