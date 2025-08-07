#pragma once
#include "ints.h"

typedef struct {
	u32 visit_id; // keeps track of the next available visit node
	u32 last_indirection_id; // keeps track of the last indirect dependency
	u32 last_opaque_id; // keeps track of the last opaque dependency (like structs) that enable circular types
	u32 last_fn_id; // keep track of the last const function running (any cycle detection with it in a type is an immedate failure
	u32 recursion_count; // keeps track of the number of const functions in flight
} VisitorState;
