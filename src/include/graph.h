#pragma once
#include "ast.h"
#include "sema.h"
#include "type.h"

TypeHandle resolve_type_sig_graph(SemaCtx * ctx, TypeSig * sig);
bool resolve_type_alias_graph(SemaCtx * ctx, TypeAlias * alias);
bool resolve_var_graph(SemaCtx * ctx, Var * var);
