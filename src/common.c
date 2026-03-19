#include "include/common.h"
#include "include/debug.h"

bool src_span_is_valid(const SrcSpan * span) {
	return span->begin <= span->end;
}

VisitorState visitor_state_new(void) {
	return (VisitorState){
		.last_indirection_id = 0,
		.last_opaque_id = 0,
		.visit_id = 1,
	};
}

VisitOpaque visitor_opaque(VisitorState * visitor) {
	VisitIndex id = visitor->visit_id++;
	VisitIndex last_opaque = visitor->last_opaque_id;
	visitor->last_opaque_id = id;
	return (VisitOpaque){.visit_id = id, .last_opaque = last_opaque};
}

VisitStructural visitor_structural(VisitorState * visitor) {
	VisitIndex id = visitor->visit_id++;
	return (VisitStructural){.visit_id = id};
}

bool visitor_check_opaque(const VisitorState * visitor, VisitIndex idx) {
	return idx <= visitor->last_indirection_id;
}

bool visitor_check_structural(const VisitorState * visitor, VisitIndex idx) {
	ASSERT(idx != visitor->last_opaque_id);
	return idx < visitor->last_opaque_id && idx <= visitor->last_indirection_id;
}

void visitor_opaque_restore(VisitorState * visitor, VisitOpaque checkpoint) {
	--visitor->visit_id;
	ASSERT(visitor->visit_id == checkpoint.visit_id);
	visitor->last_opaque_id = checkpoint.last_opaque;
}

void visitor_structural_restore(VisitorState * visitor,
								VisitStructural checkpoint) {
	--visitor->visit_id;
	ASSERT(visitor->visit_id == checkpoint.visit_id);
}

VisitIndex visitor_push_indirection(VisitorState * visitor) {
	VisitIndex id = visitor->last_opaque_id;
	visitor->last_opaque_id = visitor->visit_id++;
	return id;
}

void visitor_pop_indirection(VisitorState * visitor, VisitIndex idx) {
	--visitor->visit_id;
	visitor->last_opaque_id = idx;
}
