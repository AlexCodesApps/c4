#include <stdbool.h>
#ifdef _WIN32

typedef struct {
} DirIter;

#else // Only Windows and UNIX Support
#include <dirent.h>
typedef struct {
	DIR * dir;
	struct dirent * entry;
} DirWalker;
#endif

bool dir_walker_open(const char * path, DirWalker * out);
// Must be called before dir_iter_advance blame WIN32 API
const char * dir_walker_name(DirWalker * walker);
bool dir_walker_next(DirWalker * walker);
void dir_walker_close(DirWalker * walker);
