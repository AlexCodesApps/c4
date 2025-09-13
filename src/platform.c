#include "include/platform.h"

#ifdef _WIN32

#else
#include <errno.h>
#include <stddef.h>

bool dir_walker_open(const char * path, DirWalker * out) {
	DIR * dir = opendir(path);
	if (!dir) return false;
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

void dir_walker_close(DirWalker * walker) {
	closedir(walker->dir);
}

#endif
