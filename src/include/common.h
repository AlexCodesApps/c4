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
} VisitorState;

typedef struct {
	VisitIndex visit_id;
	VisitIndex last_opaque;
} VisitOpaque;

typedef struct {
	VisitIndex visit_id;
} VisitStructural;

typedef struct {
	TokenIndex begin;
	TokenIndex end;
} SrcSpan;

bool src_span_is_valid(const SrcSpan * span);

#define INVALID_SRC_SPAN ((SrcSpan){TOKEN_INDEX_MAX, 0})

VisitorState visitor_state_new(void);

VisitOpaque visitor_opaque(VisitorState * visitor);
VisitStructural visitor_structural(VisitorState * visitor);

bool visitor_check_opaque(const VisitorState * visitor, VisitIndex idx);
bool visitor_check_structural(const VisitorState * visitor, VisitIndex idx);

void visitor_opaque_restore(VisitorState * visitor, VisitOpaque checkpoint);
void visitor_structural_restore(VisitorState * visitor,
								VisitStructural checkpoint);

// This is not its visit id!! You've been warned!!
VisitIndex visitor_push_indirection(VisitorState * visitor);
void visitor_pop_indirection(VisitorState * visitor, VisitIndex idx);
