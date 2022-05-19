#ifndef _synchronize_h_INCLUDED
#define _synchronize_h_INCLUDED

#include <pthread.h>

struct ring;
struct ruler;

struct synchronize
{
  pthread_mutex_t mutex;
  pthread_cond_t condition;
  volatile void (*function)(struct ring*);
  volatile unsigned count;
  const char * name;
  unsigned size;
};

void init_synchronize (struct synchronize *, unsigned participants);

void rendezvous (struct ring *,
                 struct synchronize *,
                 void(*function)(struct ring*), const char*);

void disable_synchronize (struct synchronize *);

#endif
