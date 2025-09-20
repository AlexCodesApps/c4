#include "include/vm.h"
#include "include/utility.h"

bool vm_complete_type_iter(TypeList * queue, VMemArena * arena, VM * vm,
						   Type * type) {
	switch (type->pass) {
	case TYPE_PASS_CHECKED:
		switch (type->kind) {
		case TYPE_BUILTIN_VOID:
			type->evaluated.size = 0;
			type->evaluated.align = 0;
			type->pass = TYPE_PASS_EVALUATED;
			break;
		case TYPE_BUILTIN_I32:
			type->evaluated.size = 4;
			type->evaluated.align = 4;
			type->pass = TYPE_PASS_EVALUATED;
			break;
		case TYPE_PTR:
			type->evaluated.size = 8;
			type->evaluated.align = 8;
			type->pass = TYPE_PASS_EVALUATED;
			break;
		case TYPE_REF:
			type->evaluated.size = 8;
			type->evaluated.align = 8;
			type->pass = TYPE_PASS_EVALUATED;
			break;
		}
		type->pass = TYPE_PASS_EVALUATED;
		FALLTHROUGH();
	case TYPE_PASS_EVALUATED:
		return true;
	}
}

void vm_init(VM * vm) { (void)vm; }
