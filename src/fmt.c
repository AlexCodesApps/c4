#include "include/fmt.h"
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
			ASSERT(next(&path) == 'i');
			TokenIndex ti = va_arg(va, TokenIndex);
			_Generic(ti,
				u32: fprintf(file, "%" PRIu32, ti),
				default: FAIL("TokenIndex format needs to be updated"));
			continue;
		case 'i':
			switch (next(&path)) {
			case 'w': {
				int i = va_arg(va, int);
				fprintf(file, "%d", i);
				continue;
			}
			case 'q': {
				i64 i = va_arg(va, i64);
				fprintf(file, "%" PRIi64, i);
				continue;
			}
			case 'd': {
				ASSERT(next(&path) == 'q');
				TODO();
			}
			default:
				UNREACHABLE();
			}
		case 'u':
			switch (next(&path)) {
			case 'w': {
				unsigned int i = va_arg(va, unsigned int);
				fprintf(file, "%u", i);
				continue;
			}
			case 'q': {
				u64 i = va_arg(va, u64);
				fprintf(file, "%" PRIu64, i);
				continue;
			}
			case 'd': {
				ASSERT(next(&path) == 'q');
				TODO();
			}
			default:
				UNREACHABLE();
			}
		}
	}
}

// | FORMAT   | USAGE                              |
// |----------|------------------------------------|
// | %uw      | print integer u* <= u32            |
// | %uq      | print integer u64                  |
// | %iw      | print integer u* <= i32            |
// | %iq      | print integer i64                  |
// | %idq     | print integer i128                 |
// | %s print | Str                                |
// | %cs      | print const char *                 |
// | %ch      | print ascii code of integer <= *32 |
// | %%       | print '%'                          |
// | %ti      | print TokenIndex                   |
void c4printf(FILE * file, const char * path, ...) {
	va_list va;
	va_start(va, path);
	c4vaprintf(file, path, va);
	va_end(va);
}
