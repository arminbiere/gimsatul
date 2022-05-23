#ifndef _barrier_h_INCLUDED
#define _barrier_h_INCLUDED

#include <stdbool.h>
#include <pthread.h>

struct ring;
struct ruler;

struct barrier
{
  const char * name;
  pthread_mutex_t mutex;
  pthread_cond_t condition;
  volatile unsigned waiting;
  unsigned size;
  bool disabled;
  bool current;
};

void init_barrier (struct barrier *, const char * name, unsigned size);
void rendezvous (struct barrier *, struct ring *);
void abort_waiting_and_disable_barrier (struct barrier *);

#endif
