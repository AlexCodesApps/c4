#include "platform.h"
#include <stdbool.h>

#if defined(PLATFORM_WINDOWS)
#include <windows.h>

typedef struct {
	HANDLE handle;
	WIN32_FIND_DATA data;
} DirWalker;

#elif defined(PLATFORM_UNIX)
#include <dirent.h>

typedef struct {
	DIR * dir;
	struct dirent * entry;
} DirWalker;
#else
#error unknown platform
#endif

bool dir_walker_open(const char * path, DirWalker * out);
// Must be called before dir_iter_next. Blame WIN32 API.
// This seems faulty in case of zero entries, but '.' and '..' ensure
// that failure case impossible. I think.
const char * dir_walker_name(DirWalker * walker);
bool dir_walker_next(DirWalker * walker);
void dir_walker_close(DirWalker * walker);
