#include "src/include/ast.h"
#include "src/include/sema.h"
#include "src/include/utility.h"
#include "src/include/debug.h" // IWYU pragma: keep
#include <stdio.h>
#include <dirent.h>
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

bool process_src(VMemArena * arena, Str src) {
	// dump_tokens(src);
	Parser parser;
	parser_init(&parser, src, arena);
	Ast ast = parser_run(&parser);
	bool had_error = parser.had_error;
	fputs(had_error ? "parse failed\n" : "parse succeded\n", stderr);
	// dump_ast(ast);
	SemaTypeInternTable type_table;
	SemaEnv env;
	SemaCtx ctx;
	sema_type_intern_table_init(&type_table);
	sema_env_init(&env);
	sema_ctx_init(&ctx, arena, &type_table, &env);
	bool sema_result = sema_analyze_ast(&ctx, ast);
	if (!sema_result) {
		fprintf(stderr, "semantic analysis failed\n");
		return false;
	}
	fprintf(stderr, "semantic analysis succeeded\n");
	// lower smhow
	return !had_error;
}

int process_path(VMemArena * arena, const char * path) {
	Str src;
	if (!read_file(arena, path, &src)) {
		fprintf(stderr, "error: unable to open file '%s'\n", path);
		return 2;
	}
	return process_src(arena, src) ? 0 : 1;
}

void usage(const char * program) {
	fprintf(stderr, "usage : %s (test|compile file)?\n", program);
	exit(1);
}

bool run_tests(VMemArena * arena, const char * should_fail_path, const char * should_succeed_path) {
	DIR * sf_dir = opendir(should_fail_path);
	if (!sf_dir) {
		fprintf(stderr, "error: unable to open directory '%s'\n", should_fail_path);
		return false;
	}
	DIR * ss_dir = opendir(should_succeed_path);
	bool result = false;
	if (!ss_dir) {
		fprintf(stderr, "error: unable to open directory '%s'\n", should_succeed_path);
		goto cleanup_sf;
	}
	struct dirent * dirent;
	fprintf(stderr, "=== FAILURE CASES ===\n");
	while ((dirent = readdir(sf_dir))) {
		if (strcmp(dirent->d_name, ".") == 0
				|| strcmp(dirent->d_name, "..") == 0) {
			continue;
		}
		char path[256];
		if (snprintf(path, 256, "%s/%s", should_fail_path, dirent->d_name) < 1) {
			fprintf(stderr, "error: buffer to small for path 'test/%s'\n", dirent->d_name);
			goto cleanup;
		}
		fprintf(stderr, "compiling file '%s'\n", path);
		int compile_result = process_path(arena, path);
		if (compile_result == 2) { // IO error
			goto cleanup;
		}
		if (compile_result == 0) { // Compile Success
			fprintf(stderr, "error: '%s' should not have compiled\n", path);
			goto cleanup;
		}
		vmem_arena_reset(arena);
	}
	fprintf(stderr, "=== SUCCESS CASES ===\n");
	while ((dirent = readdir(ss_dir))) {
		if (strcmp(dirent->d_name, ".") == 0
				|| strcmp(dirent->d_name, "..") == 0) {
			continue;
		}
		char path[256];
		if (snprintf(path, 256, "%s/%s", should_succeed_path, dirent->d_name) < 1) {
			fprintf(stderr, "error: buffer to small for path 'test/%s'\n", dirent->d_name);
			goto cleanup;
		}
		fprintf(stderr, "compiling file '%s'\n", path);
		int compile_result = process_path(arena, path);
		if (compile_result == 2) { // IO error
			goto cleanup;
		}
		if (compile_result == 1) { // Compile Failure
			fprintf(stderr, "error: '%s' did not compile\n", path);
			goto cleanup;
		}
		vmem_arena_reset(arena);
	}
	result = true;
cleanup:
	closedir(ss_dir);
cleanup_sf:
	closedir(sf_dir);
	return result;
}

int main(int argc, char ** argv) {
	const char * program = argv[0];
	if (argc  > 3) {
		usage(program);
	}
	const char * cmd = "test";
	if (argc > 1) {
		cmd = argv[1];
	}
	if (strcmp(cmd, "compile") == 0) {
		if (argc != 3) {
			usage(program);
		}
		const char * path = argv[2];
		VMemArena arena;
		if (!vmem_arena_init(&arena, MB(5))) {
			abort();
		}
		int result = process_path(&arena, path);
		vmem_arena_free(&arena);
		return result;
	} else if (strcmp(cmd, "test") == 0) {
		VMemArena arena;
		if (!vmem_arena_init(&arena, MB(5))) {
			abort();
		}
		bool result = run_tests(&arena, "test/fail", "test/ok");
		if (result) {
			fprintf(stderr, "all tests succeeded\n");
		} else {
			fprintf(stderr, "test failed\n");
		}
		return result ? 0 : 1;
	}
	usage(program);
}
