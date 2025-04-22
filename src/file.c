#include "include/file.h"
#include <linux/limits.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <threads.h>
#include <unistd.h>
#include <string.h>

File file_open(Str path, FileMode mode) {
    static thread_local char buffer[PATH_MAX + 1];
    if (path.size > PATH_MAX) {
        return (File){ -1 };
    }
    memcpy(buffer, path.data, path.size);
    buffer[path.size] = '\0';
    return file_open_with_cstr(buffer, mode);
}

File file_open_with_cstr(const char * path, FileMode mode) {
    int unix_mode = 0;
    if (mode.read && mode.write) {
        unix_mode |= O_RDWR;
    }
    else if (mode.write) {
        unix_mode |= O_WRONLY;
    } else if (mode.read) {
        unix_mode |= O_RDONLY;
    }
    if (mode.create) {
        unix_mode |= O_CREAT;
    }
    if (mode.truncate) {
        unix_mode |= O_TRUNC;
    } else {
        unix_mode |= O_APPEND;
    }
    int fd = open(path, unix_mode, 0777);
    return file_from_descriptor(fd);
}

File file_from_descriptor(FileDescriptor descriptor) {
    return (File) { descriptor };
}

bool file_is_valid(File file) {
    return file.fd != -1;
}

void file_close(File file) {
    close(file.fd);
}

int file_read(File file, void * buff, usize size) {
    return read(file.fd, buff, size);
}

bool file_write(File file, const void * buff, usize size) {
    return write(file.fd, buff, size) >= 0;
}

File stdout_file() {
    return file_from_descriptor(STDOUT_FILENO);
}

File stdin_file() {
    return file_from_descriptor(STDOUT_FILENO);
}

File stderr_file() {
    return file_from_descriptor(STDERR_FILENO);
}

File invalid_file() {
    return file_from_descriptor(-1);
}

isize file_get_size(File file) {
    int fd = file.fd;
    struct stat s;
    int status = fstat(fd, &s);
    if (status != 0) {
        return FILE_IO_ERROR;
    }
    return s.st_size;
}
