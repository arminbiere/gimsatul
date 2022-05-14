#include "bump.h"
#include "logging.h"
#include "ring.h"

static void
rescale_variable_scores (struct ring *ring)
{
  struct queue *queue = &ring->queue;
  unsigned stable = ring->stable;
  double max_score = queue->increment[stable];
  struct node *nodes = queue->nodes;
  struct node *end = nodes + ring->size;
  for (struct node * node = nodes; node != end; node++)
    if (node->score > max_score)
      max_score = node->score;
  LOG ("rescaling by maximum score of %g", max_score);
  assert (max_score > 0);
  for (struct node * node = nodes; node != end; node++)
    node->score /= max_score;
  queue->increment[stable] /= max_score;
}

void
bump_variable_score (struct ring *ring, unsigned idx)
{
  struct queue *queue = &ring->queue;
  struct node *node = queue->nodes + idx;
  double old_score = node->score;
  double new_score = old_score + queue->increment[ring->stable];
  LOG ("bumping %s old score %g to new score %g",
       LOGVAR (idx), old_score, new_score);
  update_queue (queue, node, new_score);
  if (new_score > MAX_SCORE)
    rescale_variable_scores (ring);
}

void
swap_scores (struct ring *ring)
{
  struct queue *queue = &ring->queue;
  struct node * nodes = queue->nodes;
  double *scores = queue->scores;
  for (all_active_nodes (node))
    {
      double tmp = node->score;
      unsigned idx = node - nodes;
      double * s = scores + idx;
      node->score = *s;
      node->child = node->prev = node->next = 0;
      *s = tmp;
    }
  queue->root = 0;
  for (all_active_nodes (node))
    push_queue (queue, node);
  double tmp = queue->increment[0];
  queue->increment[0] = queue->increment[1];
  queue->increment[1] = tmp;
}

void
bump_score_increment (struct ring *ring)
{
  struct queue *queue = &ring->queue;
  unsigned stable = ring->stable;
  double old_increment = queue->increment[stable];
  double factor = stable ? 1.0 / STABLE_DECAY : 1.0 / FOCUSED_DECAY;
  double new_increment = old_increment * factor;
  LOG ("new increment %g", new_increment);
  queue->increment[stable] = new_increment;
  if (queue->increment[stable] > MAX_SCORE)
    rescale_variable_scores (ring);
}

