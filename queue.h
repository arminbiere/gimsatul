#ifndef _queue_h_INCLUDED
#define _queue_h_INCLUDED

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>

struct link
{
  struct link * prev, * next;
  uint64_t stamp;
};

struct queue
{
  struct link * links;
  struct link * first, * last;
  struct link * search;
  uint64_t stamp;
};

void enqueue (struct queue * queue, struct link * link, bool update);
void dequeue (struct queue * queue, struct link * link);


void
update_queue_search (struct queue * queue, struct link * link)
{
  assert (queue->search);
  if (queue->stamp < link->stamp)
    queue->stamp = link->stamp;
}

#endif
