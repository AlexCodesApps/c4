#include "include/fmt.h"
#include "include/ast.h"
#include "include/debug.h"
#include "include/lexer.h"
#include "include/utility.h"
#include <inttypes.h>
#include <stdarg.h>

void c4print(FILE * file, const char * msg) { fputs(msg, file); }

void c4println(FILE * file, const char * msg) {
	fputs(msg, file);
	fputc('\n', file);
	fflush(file);
}

static char next(const char ** iter) {
	char c = **iter;
	if (c != '\0') {
		++(*iter);
	}
	return c;
}

void c4print_decimal(FILE * file, bool minus, I128 i) {
	char buffer[40]; // enough to fit largest I128 + sign
	char * cursor = buffer;
	if (minus) {
		*cursor++ = '-';
	}
	if (!i.high) {
		u64 exp = 1;
		for (u64 accum = i.low / 10; accum; accum /= 10) {
			exp *= 10;
		}
		do {
			word digit = (i.low / exp) % 10;
			*cursor++ = '0' + (u8)digit;
			exp /= 10;
		} while (exp);
	} else {
		I128 exp = i128_new(0, 1);
		for (I128 accum = i128_div_by_10(i); !i128_iszero(accum);
			 accum = i128_div_by_10(accum)) {
			ASSERT(i128_mul_by_10(&exp));
		}
		do {
			I128 tmp = i;
			i = i128_div_rem(&tmp, exp);
			ASSERT(tmp.high == 0);
			ASSERT(tmp.low / 10 == 0);
			*cursor++ = '0' + (u8)tmp.low;
			exp = i128_div_by_10(exp);
		} while (!i128_iszero(exp));
	}
	fwrite(buffer, 1, (usize)(cursor - buffer), file);
}

void c4print_type_sig(FILE * file, TypeSig * sig) {
	if (sig->is_mut) {
		c4print(file, "mut ");
	}
	switch (sig->pass) {
	case TYPE_SIG_PASS_ERROR:
		FAIL("<error>");
	case TYPE_SIG_PASS_PARSED:
	case TYPE_SIG_PASS_CYCLE_CHECKED:
		switch (sig->kind) {
		case TYPE_SIG_PTR:
			c4print(file, "*");
			c4print_type_sig(file, sig->as.ptr_like);
			break;
		case TYPE_SIG_REF:
			c4print(file, "&");
			c4print_type_sig(file, sig->as.ptr_like);
			break;
		case TYPE_SIG_IDEN:
			c4printf(file, "%s", sig->as.iden);
			break;
		case TYPE_SIG_VOID:
			c4print(file, "void");
			break;
		case TYPE_SIG_FN:
			c4print(file, "fn(");
			// on overflow the loop is skipped
			usize last_idx = sig->as.fn.params.size - 1;
			for (usize i = 0; i < sig->as.fn.params.size; ++i) {
				TypeSig * ty = type_sig_list_at(&sig->as.fn.params, i);
				c4print_type_sig(file, ty);
				if (i != last_idx)
					c4print(file, ", ");
			}
			c4print(file, "): ");
			c4print_type_sig(file, sig->as.fn.return_ty);
			break;
		case TYPE_SIG_ALIAS_STUB:
		case TYPE_SIG_TYPE_STUB:
			break;
		}
		break;
	}
}

void c4print_type_handle(FILE * file, TypeHandle handle) {
	if (handle.is_mut) {
		c4print(file, "mut ");
	}
	switch (handle.type->pass) {
	case TYPE_PASS_ERROR:
		c4print(file, "<error>");
		break;
	case TYPE_PASS_CHECKED:
	case TYPE_PASS_EVALUATED:
		switch (handle.type->kind) {
		case TYPE_BUILTIN_VOID:
			c4print(file, "void");
			break;
		case TYPE_BUILTIN_I32:
			c4print(file, "i32");
			break;
		case TYPE_PTR:
			c4print(file, "*");
			c4print_type_handle(file, handle.type->as.ptr_like);
			break;
		case TYPE_REF:
			c4print(file, "&");
			c4print_type_handle(file, handle.type->as.ptr_like);
			break;
		case TYPE_FN:
			c4print(file, "fn(");
			// on overflow the loop is skipped
			usize last_idx = handle.type->as.fn.params.size - 1;
			for (usize i = 0; i < handle.type->as.fn.params.size; ++i) {
				TypeHandle ty = handle.type->as.fn.params.data[i];
				c4print_type_handle(file, ty);
				if (i != last_idx)
					c4print(file, ", ");
			}
			c4print(file, "): ");
			c4print_type_handle(file, handle.type->as.fn.return_ty);
			break;
		}
	}
}

void c4vaprintf(FILE * file, const char * path, va_list va) {
	while (*path != '\0') {
		char c = next(&path);
		if (c != '%') {
			putc(c, file);
			continue;
		}
		switch (next(&path)) {
		case '%':
			fputc('%', file);
			continue;
		case 's': {
			Str str = va_arg(va, Str);
			fwrite(str.data, 1, str.size, file);
			continue;
		}
		case 'c':
			switch (next(&path)) {
			case 's': {
				const char * ptr = va_arg(va, const char *);
				fputs(ptr, file);
				continue;
			}
			case 'h': {
				int c = va_arg(va, int);
				putc(c, file);
				continue;
			}
			default:
				UNREACHABLE();
			}
		case 't':
			switch (next(&path)) {
			case 'i': {
				STATIC_ASSERT(sizeof(TokenIndex) == sizeof(u32),
							  "TokenIndex format needs to be updated");
				goto case_uw;
				break;
			}
			case 's': {
				TypeSig * sig = va_arg(va, TypeSig *);
				c4print_type_sig(file, sig);
				break;
			}
			case 'h': {
				TypeHandle handle = va_arg(va, TypeHandle);
				c4print_type_handle(file, handle);
				break;
			}
			default:
				UNREACHABLE();
			}
			break;
		case 'i':
			switch (next(&path)) {
			case 'w': {
				i64 i = va_arg(va, int);
				bool minus = false;
				if (i < 0) {
					i = -i;
					minus = true;
				}
				c4print_decimal(file, minus, i128_new(0, (u64)i));
				continue;
			}
			case 'q': {
				i64 i = va_arg(va, i64);
				u64 u = (u64)i;
				bool minus = false;
				if (i < 0) {
					u = -(u64)i; // to avoid invoking UB
					minus = true;
				}
				c4print_decimal(file, minus, i128_new(0, u));
				continue;
			}
			default:
				UNREACHABLE();
			}
		case 'u':
			switch (next(&path)) {
			case_uw:
			case 'w': {
				unsigned int i = va_arg(va, unsigned int);
				c4print_decimal(file, false, i128_new(0, i));
				continue;
			}
			case 'q': {
				u64 i = va_arg(va, u64);
				c4print_decimal(file, false, i128_new(0, i));
				continue;
			}
			case 'd': {
				ASSERT(next(&path) == 'q');
				I128 i = va_arg(va, I128);
				c4print_decimal(file, false, i);
				continue;
			}
			default:
				UNREACHABLE();
			}
		case 'p': {
			void * ptr = va_arg(va, void *);
			fprintf(file, "%p", ptr);
			continue;
		}
		default:
			UNREACHABLE();
		}
	}
}

// | FORMAT   | USAGE                              |
// |----------|------------------------------------|
// | %uw      | print integer u* <= u32            |
// | %uq      | print integer u64                  |
// | %iw      | print integer i* <= i32            |
// | %iq      | print integer i64                  |
// | %idq     | print integer i128                 |
// | %s print | Str                                |
// | %cs      | print const char *                 |
// | %ch      | print ascii repr of integer <= *32 |
// | %%       | print '%'                          |
// | %ti      | print TokenIndex                   |
void c4printf(FILE * file, const char * path, ...) {
	va_list va;
	va_start(va, path);
	c4vaprintf(file, path, va);
	va_end(va);
}
