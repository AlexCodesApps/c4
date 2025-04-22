#pragma once
#include "str.h"
#include "writer.h"
#include <stdio.h>

struct File {
    int fd;
} typedef File;

typedef int FileDescriptor;

struct FileMode {
    bool read : 1;
    bool write : 1;
    bool truncate : 1;
    bool create : 1;
} typedef FileMode;

#define END_OF_FILE 0
#define FILE_IO_ERROR (-1)

File file_open(Str path, FileMode mode);
File file_open_with_cstr(const char *, FileMode mode);
File file_from_descriptor(FileDescriptor descriptor);
bool file_is_valid(File file);
void file_close(File file);
bool file_write(File file, const void * buff, usize size);
int file_read(File file, void * buff, usize size);
isize file_get_size(File file);

File stdout_file();
File stdin_file();
File stderr_file();
File invalid_file();

Writer file_writer(File file);
Writer cfile_writer(FILE file[ref]);

Writer stdout_writer();
Writer stderr_writer();
