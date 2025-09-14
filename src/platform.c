#include "include/platform.h"

#ifdef _WIN32
#include <stdio.h>

bool dir_walker_open(const char * path, DirWalker * out) {
	char buf[1024]; // need to copy file to add wildcard
	if (snprintf(buf, 1024, "%s/*", path) < 1) {
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
	FindNextFile(walker->handle, &walker->data);
}

#else
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

#endif
