#include "src/include/asm.h"
#include "src/include/debug.h"
#include "src/include/ast.h"
#include "src/include/sema.h"
#include "src/include/utility.h"
#include <stdio.h>
#include <stdlib.h>
#include <dirent.h>

bool read_file(VMemArena * arena, const char * path, Str * out) {
	bool status = false;
	FILE * file = fopen(path, "r");
	if (!file) {
		return false;
	}
	if (fseek(file, 0, SEEK_END) != 0) {
		goto cleanup;
	}
	long lsize = ftell(file);
	if (lsize == -1) {
		goto cleanup;
	}
	if (lsize == 0) {
		*out = s("");
		status = true;
		goto cleanup;
	}
	usize size = (usize)lsize;
	char * buf = vmem_arena_alloc_bytes(arena, size, alignof(char));
	if (!buf) {
		goto cleanup;
	}
	rewind(file);
	if (fread(buf, 1, size, file) == 0) {
		goto cleanup;
	}
	*out = str_new(buf, size);
	status = true;
cleanup:
	fclose(file);
	return status;
}

bool process_src(VMemArena * arena, Str src) {
	dump_tokens(src);
	Parser parser;
	parser_init(&parser, src, arena);
	Ast ast = parser_run(&parser);
	fputs(parser.had_error ? "parse failed\n" : "parse succeded\n", stderr);
	dump_ast(ast);
	SemaTypeInternTable type_table;
	SemaDeclList decl_list;
	SemaCtx ctx;
	sema_type_intern_table_init(&type_table);
	sema_decl_list_init(&decl_list);
	sema_ctx_init(&ctx, arena, &type_table, &decl_list);
	bool sema_result = sema_analyze_ast(&ctx, ast);
	if (!sema_result) {
		fprintf(stderr, "semantic analysis failed\n");
		return false;
	}
	fprintf(stderr, "semantic analysis succeeded\n");
	lower_to_asm(stderr, decl_list);
	return true;
}

void usage(const char * program) {
	fprintf(stderr, "usage : %s ((compile file?)|test)?\n", program);
	exit(1);
}

int main(int argc, char ** argv) {
	const char * program = argv[0];
	if (argc  > 3) {
		usage(program);
	}
	const char * cmd = "compile";
	if (argc > 1) {
		cmd = argv[1];
	}
	if (strcmp(cmd, "compile") == 0) {
		const char * path = "test/design.txt";
		if (argc == 3) {
			path = argv[2];
		}
		VMemArena arena;
		if (!vmem_arena_init(&arena, MB(5))) {
			abort();
		}
		Str src;
		if (!read_file(&arena, path, &src)) {
			fprintf(stderr, "error: unable to open file '%s'\n", path);
			vmem_arena_free(&arena);
			return 1;
		}
		bool result = process_src(&arena, src);
		vmem_arena_free(&arena);
		return result ? 0 : 1;
	} else if (strcmp(cmd, "test") == 0) {
		DIR * dir = opendir("test");
		if (!dir) {
			fprintf(stderr, "error: unable to open 'test' directory");
			return 1;
		}
		struct dirent * dirent;
		char path[256];
		VMemArena arena;
		if (!vmem_arena_init(&arena, MB(5))) {
			abort();
		}
		while ((dirent = readdir(dir))) {
			if (strcmp(dirent->d_name, "..") == 0
				|| strcmp(dirent->d_name, ".") == 0) {
				continue;
			}
			int written = snprintf(path, 256, "test/%s", dirent->d_name);
			if (written < 1) {
				fprintf(stderr, "error: buffer to small for path 'test/%s'\n", dirent->d_name);
				vmem_arena_free(&arena);
				closedir(dir);
				return 1;
			}
			Str src;
			if (!read_file(&arena, path, &src)) {
				fprintf(stderr, "error: unable to open file '%s'\n", path);
				vmem_arena_free(&arena);
				closedir(dir);
				return 1;
			}
			process_src(&arena, src);
			vmem_arena_reset(&arena);
		}
		vmem_arena_free(&arena);
		closedir(dir);
	}
	return 0;
}
