#include "include/common.h"

VisitorState visitor_state_new(void) {
	return (VisitorState){
		.last_fn_id = 0,
		.last_indirection_id = 0,
		.last_opaque_id = 0,
		.visit_id = 1,
		.recursion_count = 0,
	};
}
