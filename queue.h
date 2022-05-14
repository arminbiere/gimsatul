#ifndef _queue_h_INCLUDED
#define _queue_h_INCLUDED

#include <assert.h>
#include <stdbool.h>

struct node
{
  double score;
  struct node *child, *prev, *next;
};

struct queue
{
  double increment[2];
  struct node *nodes;
  struct node *root;
  double *scores;
};

/*------------------------------------------------------------------------*/

void pop_queue (struct queue *, struct node *);
void push_queue (struct queue *, struct node *node);
void update_queue (struct queue *, struct node *, double new_score);

/*------------------------------------------------------------------------*/

static inline bool
queue_contains (struct queue *queue, struct node *node)
{
  return queue->root == node || node->prev;
}

#endif
