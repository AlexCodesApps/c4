#include "include/dir_walker.h"
#include "include/platform.h"

#if defined(PLATFORM_WINDOWS)
#include "include/utility.h"

bool dir_walker_open(const char * path, DirWalker * out) {
	char buf[MAX_PATH]; // need to copy file to add wildcard
	if (!snprintf_bool(buf, MAX_PATH, "%s/*", path)) {
		return false; // just fail if too big
	}
	WIN32_FIND_DATA data;
	HANDLE handle = FindFirstFile(buf, &data);
	if (handle == INVALID_HANDLE_VALUE) {
		return false;
	}
	out->data = data;
	out->handle = handle;
	return true;
}

const char * dir_walker_name(DirWalker * walker) {
	return walker->data.cFileName;
}

void dir_walker_close(DirWalker * walker) { FindClose(walker->handle); }

bool dir_walker_next(DirWalker * walker) {
	return FindNextFile(walker->handle, &walker->data);
}

#elif defined(PLATFORM_UNIX)
#include <errno.h>
#include <stddef.h>

bool dir_walker_open(const char * path, DirWalker * out) {
	DIR * dir = opendir(path);
	if (!dir)
		return false;
	errno = 0;
	struct dirent * ent = readdir(dir);
	if (errno) {
		closedir(dir);
		return false;
	}
	out->dir = dir;
	out->entry = ent;
	return true;
}

const char * dir_walker_name(DirWalker * walker) {
	return walker->entry->d_name;
}

bool dir_walker_next(DirWalker * walker) {
	walker->entry = readdir(walker->dir);
	return walker->entry != NULL;
}

void dir_walker_close(DirWalker * walker) { closedir(walker->dir); }

#else
#error unknown platform
#endif
