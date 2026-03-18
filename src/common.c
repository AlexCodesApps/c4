#include "include/common.h"

bool src_span_is_valid(const SrcSpan * span) {
	return span->begin <= span->end;
}

VisitorState visitor_state_new(void) {
	return (VisitorState){
		.last_fn_id = 0,
		.last_indirection_id = 0,
		.last_opaque_id = 0,
		.visit_id = 1,
		.recursion_count = 0,
	};
}

VisitIndex visitor_opaque(VisitorState * visitor) {
	VisitIndex id = visitor->visit_id++;
	visitor->last_opaque_id = id;
	return id;
}
