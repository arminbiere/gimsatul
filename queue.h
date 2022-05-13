#ifndef _queue_h_INCLUDED
#define _queue_h_INCLUDED

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

#endif
