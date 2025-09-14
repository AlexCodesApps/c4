#include "src/include/parser.h"
#include "src/include/utility.h"
#include "src/include/debug.h" // IWYU pragma: keep
#include "src/include/platform.h"
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
	char * buf = vmem_arena_alloc_bytes(arena, size, _Alignof(char));
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

bool process_src(VMemArena * arena, const char * path, Str src) {
	Ast ast;
	ParseResult parse_result = parse_src(arena, str_from_cstr(path), src, &ast);
	switch (parse_result) {
	case PARSE_RESULT_OK:
		break;
	case PARSE_RESULT_ERROR:
		return false;
	case PARSE_RESULT_OOM:
		fprintf(stderr, "fatal error: Out Of Memory\n");
		fprintf(stderr, "exiting ...\n");
	exit(1);
	case PARSE_RESULT_OVERFLOW:
		fprintf(stderr, "fatal error: internal integer overflow\n");
		fprintf(stderr, "You have likely reached the limits of the compiler\n");
		return false;
	}
	return true; // just finish processing here
}

int process_path(VMemArena * arena, const char * path) {
	Str src;
	if (!read_file(arena, path, &src)) {
		fprintf(stderr, "error: unable to open file '%s'\n", path);
		return 2;
	}
	return process_src(arena, path, src) ? 0 : 1;
}

void usage(const char * program) {
	fprintf(stderr, "usage : %s (test|compile file)?\n", program);
	exit(1);
}

bool run_tests(VMemArena * arena, const char * should_fail_path, const char * should_succeed_path) {
	DirWalker sf_dir;
	if (!dir_walker_open(should_fail_path, &sf_dir)) {
		fprintf(stderr, "error: unable to open directory '%s'\n", should_fail_path);
		return false;
	}
	bool result = false;
	DirWalker ss_dir;
	if (!dir_walker_open(should_succeed_path, &ss_dir)) {
		fprintf(stderr, "error: unable to open directory '%s'\n", should_succeed_path);
		goto cleanup_sf;
	}
	fprintf(stderr, "=== FAILURE CASES ===\n");
	do {
		const char * name = dir_walker_name(&sf_dir);
		if (strcmp(name, ".") == 0
				|| strcmp(name, "..") == 0) {
			continue;
		}
		char path[256];
		if (snprintf(path, 256, "%s/%s", should_fail_path, name) < 1) {
			fprintf(stderr, "error: buffer to small for path 'test/%s'\n", name);
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
	} while (dir_walker_next(&sf_dir));
	fprintf(stderr, "=== SUCCESS CASES ===\n");
	do {
		const char * name = dir_walker_name(&ss_dir);
		if (strcmp(name, ".") == 0
				|| strcmp(name, "..") == 0) {
			continue;
		}
		char path[256];
		if (snprintf(path, 256, "%s/%s", should_succeed_path, name) < 1) {
			fprintf(stderr, "error: buffer to small for path 'test/%s'\n", name);
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
	} while (dir_walker_next(&ss_dir));
	result = true;
cleanup:
	dir_walker_close(&ss_dir);
cleanup_sf:
	dir_walker_close(&sf_dir);
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
		vmem_arena_free(&arena);
		if (result) {
			fprintf(stderr, "all tests succeeded\n");
		} else {
			fprintf(stderr, "test failed\n");
		}
		return result ? 0 : 1;
	}
	usage(program);
}
