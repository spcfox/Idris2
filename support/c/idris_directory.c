#include "idris_directory.h"

#include <dirent.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

#include "idris_util.h"

char *idris2_currentDirectory() {
  DEBUG_MSG("ENTER idris2_currentDirectory(), errno = %d", errno);
  char *cwd = malloc(1024); // probably ought to deal with the unlikely event of
                            // this being too small
  IDRIS2_VERIFY(cwd, "malloc failed");
  char *res = getcwd(cwd, 1024);
  DEBUG_MSG("EXIT idris2_currentDirectory(), returning '%s', errno = %d", res, errno);
  return cwd;
}

int idris2_changeDir(char *dir) {
  DEBUG_MSG("ENTER idris2_changeDir('%s'), errno = %d", dir, errno);
  int r = chdir(dir);
  DEBUG_MSG("EXIT idris2_changeDir, returning %d, errno = %d", r, errno);
  return r;
}

int idris2_createDir(char *dir) {
#ifdef _WIN32
  return mkdir(dir);
#else
  DEBUG_MSG("ENTER idris2_createDir('%s'), errno = %d", dir, errno);
  int r = mkdir(dir, S_IRWXU | S_IRWXG | S_IRWXO);
  DEBUG_MSG("EXIT idris2_createDir, returning %d, errno = %d", r, errno);
  return r;
#endif
}

typedef struct {
  DIR *dirptr;
} DirInfo;

void *idris2_openDir(char *dir) {
  DEBUG_MSG("ENTER idris2_openDir('%s'), errno = %d", dir, errno);
  DIR *d = opendir(dir);
  if (d == NULL) {
    DEBUG_MSG("opendir failed, errno = %d", errno);
    return NULL;
  } else {
    DirInfo *di = malloc(sizeof(DirInfo));
    DEBUG_MSG("malloc %p, errno = %d", di, errno);
    IDRIS2_VERIFY(di, "malloc failed");
    di->dirptr = d;

    DEBUG_MSG("EXIT idris2_openDir, returning %p, errno = %d", di, errno);
    return (void *)di;
  }
}

void idris2_closeDir(void *d) {
  DEBUG_MSG("ENTER idris2_closeDir(%p), errno = %d", d, errno);
  DirInfo *di = (DirInfo *)d;

  IDRIS2_VERIFY(closedir(di->dirptr) == 0, "closedir failed: %s",
                strerror(errno));
  free(di);
  DEBUG_MSG("EXIT in idris2_closeDir, errno = %d", errno);
}

int idris2_removeDir(char *path) { return rmdir(path); }

char *idris2_nextDirEntry(void *d) {
  DEBUG_MSG("ENTER idris2_nextDirEntry(%p), errno = %d", d, errno);
  DirInfo *di = (DirInfo *)d;
  // `readdir` keeps `errno` unchanged on end of stream
  // so we need to reset `errno` to distinguish between
  // end of stream and failure.
  errno = 0;
  struct dirent *de = readdir(di->dirptr);

  if (de == NULL) {
    DEBUG_MSG("readdir returned NULL, errno = %d", errno);
    DEBUG_MSG("EXIT idris2_nextDirEntry, returning NULL, errno = %d", errno);
    return NULL;
  } else {
    DEBUG_MSG("EXIT idris2_nextDirEntry, returning '%s', errno = %d", de->d_name, errno);
    return de->d_name;
  }
}
