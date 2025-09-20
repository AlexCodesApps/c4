#pragma once
#include "sema.h"

bool eval_type(SemaCtx * ctx, Type * type);
bool eval_type_alias(SemaCtx * ctx, TypeAlias * alias);
bool eval_var(SemaCtx * ctx, Var * var);
bool eval_fn(SemaCtx * ctx, Fn * fn);
