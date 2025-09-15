#pragma once
#include "ast.h"
#include "type.h"

typedef struct {
	Ast * base;
	TypeInternTable * table;
	VMemArena * arena;
	VisitorState visitor;
} GraphResolverCtx;

TypeHandle resolve_type_sig_graph(GraphResolverCtx * ctx, TypeSig * sig);
bool resolve_type_alias_graph(GraphResolverCtx * ctx, TypeAlias * alias);
