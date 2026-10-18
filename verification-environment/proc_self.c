/* Container compatibility: resolve this process's own executable via /proc/self.
   Lean 4.29 uses /proc/<namespace PID>/exe; /proc here exposes host PIDs.
   No other path is changed. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <unistd.h>
#include <stdio.h>
#include <string.h>
ssize_t readlink(const char *path, char *buf, size_t size) {
    static ssize_t (*original)(const char *, char *, size_t);
    if (!original) original = dlsym(RTLD_NEXT, "readlink");
    char own[80];
    snprintf(own, sizeof own, "/proc/%d/exe", (int)getpid());
    return original(strcmp(path, own) == 0 ? "/proc/self/exe" : path, buf, size);
}
