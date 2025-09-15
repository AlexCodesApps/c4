#pragma once
#include "ints.h"
#include "lexer.h"

typedef u32 VisitIndex;

typedef struct {
	VisitIndex visit_id; // keeps track of the next available visit node
	VisitIndex
		last_indirection_id;   // keeps track of the last indirect dependency
	VisitIndex last_opaque_id; // keeps track of the last opaque dependency
							   // (like structs) that enable circular types
	VisitIndex
		last_fn_id; // keep track of the last const function running (any cycle
					// detection with it in a type is an immedate failure
	u32 recursion_count; // keeps track of the number of const functions in
						 // flight
} VisitorState;

typedef struct {
	TokenIndex begin;
	TokenIndex end;
} SrcSpan;

VisitorState visitor_state_new(void);
