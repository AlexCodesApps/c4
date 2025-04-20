#include "src/include/allocator.h"
#include "src/include/arena.h"
#include "src/include/ast.h"
#include "src/include/common.h"
#include "src/include/file.h"
#include "src/include/lexer.h"
#include "src/include/str.h"
#include "src/include/utility.h"
#include "src/include/writer.h"
#include "src/include/fmt.h"

void print_token_list(Writer writer, Str src, const TokenList list[ref]) {
    for (usize i = 0; i < list->size; ++i) {
        Token tok = list->data[i];
        Str slice = str_slice(src, tok.span.pos.index, tok.span.len);
        fmt(writer, "(token {}, row {}, col {}, src \"{}\")\n",
            token_type_to_str(tok.type), tok.span.pos.row,
            tok.span.pos.col, slice);
    }
}

void pad(Writer writer, usize padding) {
    padding *= 2;
    while (padding--) {
        writer_byte(writer, ' ');
    }
}

void print_path(Writer writer, const AstPath * path) {
    if (path->is_global) {
        fmt(writer, "::");
    }
    assert(path->list.size > 0);
    fmt(writer, "{}", path->list.data[0]);
    for (usize i = 1; i < path->list.size; ++i) {
        fmt(writer, "::{}", path->list.data[i]);
    }
}

void print_type(Writer writer, const AstType * type, usize padding) {
    pad(writer, padding);
    switch (type->type) {
    case AST_TYPE_REFERENCE:
        fmt(writer, "&\n");
        print_type(writer, type->next, padding + 1);
        break;
    case AST_TYPE_POINTER:
        fmt(writer, "*\n");
        print_type(writer, type->next, padding + 1);
        break;
    case AST_TYPE_PATH:
        print_path(writer, &type->path);
        fmt(writer, "\n");
        break;
    case AST_TYPE_FN:
        ++padding;
        fmt(writer, "fn\n");
        pad(writer, padding);
        fmt(writer, "(params)\n");
        foreach_span(&type->function.parameters, i) {
            print_type(writer, i, padding + 1);
        }
        if (type->function.has_return_type) {
            pad(writer, padding);
            fmt(writer, "(returns)\n");
            print_type(writer, type->function.return_type, padding + 1);
        }
        break;
    case AST_TYPE_POISONED:
        fmt(writer, "(poisoned type)\n");
        break;
    }
}
void print_expr(Writer writer, const AstExpr * expr, usize padding);
void print_stmt(Writer writer, const AstStmt * stmt, usize padding) {
    pad(writer, padding);
    switch (stmt->type) {
    case AST_STMT_RETURN:
        fmt(writer, "return\n");
        if (stmt->has_return_expr) {
            print_expr(writer, &stmt->return_expr, padding + 1);
        } else {
            pad(writer, padding + 1);
            fmt(writer, "(void)\n");
        }
        break;
    case AST_STMT_ASSIGNMENT:
        fmt(writer, "assign\n");
        print_expr(writer, &stmt->assign.to, padding + 1);
        print_expr(writer, &stmt->assign.from, padding + 1);
        break;
    case AST_STMT_BLOCK:
        fmt(writer, "block\n");
        foreach_span(&stmt->block, stmt) {
            print_stmt(writer, stmt, padding + 1);
        }
        break;
    case AST_STMT_EXPR:
        fmt(writer, "expr\n");
        print_expr(writer, &stmt->expr, padding + 1);
        break;
    case AST_STMT_DECL:
        fmt(writer, "{} {}\n", stmt->decl->is_const ? s("const") : s("let"),  stmt->decl->iden);
        if (stmt->decl->has_type) {
            print_type(writer, &stmt->decl->type, padding + 1);
        }
        if (stmt->decl->has_expr) {
            print_expr(writer, &stmt->decl->expr, padding + 1);
        }
        break;
    case AST_STMT_POISONED:
        fmt(writer, "(poisoned)\n");
        break;
    }
}

void print_expr(Writer writer, const AstExpr * expr, usize padding) {
    pad(writer, padding);
    switch (expr->type) {
    case AST_EXPR_FUNCTION:
        fmt(writer, "fn\n");
        pad(writer, padding + 1);
        fmt(writer, "(parameters)\n");
        foreach_span(&expr->function->params, param) {
            pad(writer, padding + 1);
            fmt(writer, "{} :\n", !str_empty(param->iden) ? param->iden : s("!"));
            print_type(writer, &param->type, padding + 2);
        }
        pad(writer, padding + 1);
        fmt(writer, "(returns)\n");
        if (expr->function->has_return_type) {
            print_type(writer, &expr->function->return_type, padding + 1);
        } else {
            pad(writer, padding + 1);
            fmt(writer, "(void)\n");
        }
        pad(writer, padding + 1);
        fmt(writer, "(body)\n");
        foreach_span(&expr->function->body, stmt) {
            print_stmt(writer, stmt, padding + 1);
        }
        break;
    case AST_EXPR_AS:
        fmt(writer, "as\n");
        print_expr(writer, expr->as.next, padding + 1);
        print_type(writer, &expr->as.type, padding + 1);
        break;
    case AST_EXPR_PATH:
        print_path(writer, &expr->path);
        fmt(writer, "\n");
        break;
    case AST_EXPR_FUNCALL:
        fmt(writer, "function call\n");
        print_expr(writer, expr->funcall.function, padding + 1);
        pad(writer, padding + 1);
        fmt(writer, "(parameters)\n");
        foreach_span(&expr->funcall.args, arg) {
            print_expr(writer, arg, padding + 1);
        }
        break;
    case AST_EXPR_POISONED:
        fmt(writer, "(poisoned)\n");
        break;
    case AST_EXPR_POISONED_NESTED:
        fmt(writer, "(poisoned nested)\n");
        break;
    case AST_EXPR_INTEGER:
        fmt(writer, "{}\n", expr->integer.value);
        break;
    case AST_EXPR_FIELD_ACCESS:
        fmt(writer, ".\n");
        print_expr(writer, expr->field_access.next, padding + 1);
        pad(writer, padding + 1);
        print_path(writer, &expr->field_access.name);
        fmt(writer, "\n");
        break;
    case AST_EXPR_UNARY:
        switch (expr->unary.type) {
        case AST_EXPR_UNARY_MINUS:
            fmt(writer, "-\n");
            break;
        case AST_EXPR_UNARY_ADDR:
            fmt(writer, "&\n");
            break;
        case AST_EXPR_UNARY_DEREF:
            fmt(writer, ".*\n");
            break;
        }
        print_expr(writer, expr->unary.next, padding + 1);
        break;
    case AST_EXPR_BINARY:
        switch (expr->binary.type) {
        case AST_EXPR_BINARY_ADD:
            fmt(writer, "+\n");
            break;
        case AST_EXPR_BINARY_SUB:
            fmt(writer, "-\n");
            break;
        }
        print_expr(writer, expr->binary.a, padding + 1);
        print_expr(writer, expr->binary.b, padding + 1);
        break;
    }
}

void print_tls_list(Writer writer, const AstTLSList * ast, usize padding) {
    Writer stderrw = file_writer(stderr_file());
    foreach_span(ast, i) {
        const AstTopLvlStmt * tls = *i;
        pad(writer, padding);
        switch (tls->type) {
        case AST_TLS_TYPE_MOD:
            fmt(writer, "mod {}\n", tls->mod.iden);
            print_tls_list(writer, &tls->mod.body, padding + 1);
            break;
        case AST_TLS_TYPE_DECL:
            fmt(writer, "{} {}\n", tls->decl.is_const ? s("const") : s("let"),  tls->decl.iden);
            if (tls->decl.has_type) {
                print_type(writer, &tls->decl.type, padding + 1);
            }
            if (tls->decl.has_expr) {
                print_expr(writer, &tls->decl.expr, padding + 1);
            }
            break;
        case AST_TLS_TYPE_POISONED:
            fmt(writer, "(poisoned tls)\n");
            break;
        }
    }
}

void print_ast(Writer writer, const Ast * ast) {
    print_tls_list(writer, &ast->list, 0);
}

int main(int argc, char ** argv) {
    Writer stderrw = stderr_writer();
    if (argc != 2) {
        fmt(stderrw, "usage : {} <file_name>\n", argv[0]);
        return 1;
    }
    Str file_name = cstr(argv[1]);
    File file = file_open(file_name, (FileMode) {
        .read = true,
        .write = false,
        .create = false,
        .truncate = false,
    });
    if (!file_is_valid(file)) {
        fmt(stderrw, "unable to open file : {}\n", file_name);
        return 1;
    }
    isize file_size = file_get_size(file);
    if (file_size == FILE_IO_ERROR) {
        fmt(stderrw, "unable to access file stats : {}\n", file_name);
        return 1;
    }
    Allocator file_allocator = general_purpose_allocator();
    char * alloc = allocator_alloc_n(file_allocator, char, file_size);
    if (!alloc) {
        fmt(stderrw, "couldn't allocate memory with size: {}\n", file_size);
        return 1;
    }
    if (file_read(file, alloc, file_size) == FILE_IO_ERROR) {
        fmt(stderrw, "unable to read file into memory : {}, size: {}\n", file_name, file_size);
        return 1;
    }
    file_close(file);
    Str src = str_new(alloc, file_size);
    Arena arena;
    usize reserved_size = MB(20);
    if (arena_new(&arena, reserved_size) != 0) {
        fmt(stderrw, "unable to reserve address space with size : {}\n", reserved_size);
        return 1;
    }
    Allocator allocator = arena_allocator(&arena);
    LexResult result = lex(allocator, src);
    if (!result.succeeded) {
        LexError err = result.err;
        switch (err.type) {
        case LEX_ERROR_OOM:
            fmt(stderrw, "arena used to capacity with size : {}\n", reserved_size);
            break;
        case LEX_ERROR_UNEXPECTED_CHAR:
            fmt(stderrw,
                "unexpected character : '{}', row: {}, col: {}\n",
                err.unexpected_char, err.pos.row, err.pos.col);
            break;
        }
        return 1;
    }
    TokenList list = result.list;
    Writer stdoutw = stdout_writer();
    print_token_list(stdoutw, src, &list);
    writer_flush(stdoutw);

    ParseResult parse_result = parse(allocator, src, token_list_to_span(&list));

    foreach_span(&parse_result.errors, err) {
        Token tok = err->unexpected_token;
        fmt(stderrw, "ERROR (token {}, row {}, col {}, src \"{}\")\n",
            token_type_to_str(tok.type), tok.span.pos.row,
            tok.span.pos.col, token_get_str(tok, src));
    }
    if (parse_result.irrecoverable) {
        switch (parse_result.irrecoverable_error) {
        case IRRECOVERABLE_PARSE_ERROR_OOM:
            fmt(stderrw, "arena used to capacity with size : {}\n", reserved_size);
            break;
        case IRRECOVERABLE_PARSE_ERROR_LIMIT_REACHED:
            fmt(stderrw, "to many errors emmited, stopping now\n");
            break;
        }
        return 1;
    }
    print_ast(stdoutw, &parse_result.ast);
    writer_flush(stdoutw);
    arena_free(&arena);
    allocator_deallocate(file_allocator, alloc);
    return 0;
}
