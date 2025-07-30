#include "src/include/debug.h"
#include "src/include/ast.h"
#include "src/include/sema.h"
#include "src/include/utility.h"
#include <stdio.h>
#include <stdlib.h>

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

int main(int argc, char ** argv) {
	if (argc  > 2) {
		fprintf(stderr, "usage : %s file?\n", argv[0]);
		return 1;
	}
	const char * path = "design.txt";
	if (argc == 2) {
		path = argv[1];
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
	dump_tokens(src);
	Parser parser;
	parser_init(&parser, src, &arena);
	Ast ast = parser_run(&parser);
	fputs(parser.had_error ? "parse failed\n" : "parse succeded\n", stderr);
	dump_ast(ast);
	SemaTypeInternTable type_table;
	SemaDeclList decl_list;
	SemaCtx ctx;
	sema_type_intern_table_init(&type_table);
	sema_decl_list_init(&decl_list);
	sema_ctx_init(&ctx, &arena, &type_table, &decl_list);
	bool sema_result = sema_analyze_ast(&ctx, ast);
	if (!sema_result) {
		fprintf(stderr, "semantic analysis failed\n");
		vmem_arena_free(&arena);
		return 1;
	}
	fprintf(stderr, "semantic analysis succeeded\n");
	vmem_arena_free(&arena);
	return 0;
}
