#include "message.h"
#include "ruler.h"

#include <string.h>

void
init_synchronization (struct synchronize *synchronize)
{
  memset (synchronize, 0, sizeof *synchronize);
  pthread_mutex_init (&synchronize->mutex, 0);
  pthread_cond_init (&synchronize->condition, 0);
}

void
disable_synchronization (struct synchronize *synchronize)
{
  if (synchronize->size < 2)
    return;
  if (pthread_mutex_lock (&synchronize->mutex))
    fatal_error ("failed to acquire synchronization lock during disabling");
  if (synchronize->count)
    {
      synchronize->function = 0;
      synchronize->name = 0;
      synchronize->count = 0;
      pthread_cond_broadcast (&synchronize->condition);
    }
  if (pthread_mutex_unlock (&synchronize->mutex))
    fatal_error ("failed to release synchronization lock during disabling");
}

void
rendezvous (struct ring *ring,
	    void (*function) (struct ring *), const char *name)
{
  struct ruler *ruler = ring->ruler;
  struct synchronize *synchronize = &ruler->synchronize;
  if (synchronize->size < 2)
    return;
  if (pthread_mutex_lock (&synchronize->mutex))
    fatal_error ("failed to acquire synchronization lock during rendezvous");

  if (synchronize->function)
    {
      if (synchronize->function != function)
	fatal_error ("trying rendezvous on '%s' but '%s' started already",
		     name, synchronize->name);
      assert (!strcmp (name, synchronize->name));
      assert (synchronize->count < synchronize->size);
      synchronize->count++;
    }
  else
    {
      assert (!synchronize->count);
      synchronize->function = function;
      synchronize->name = name;
      synchronize->count = 1;
    }

  very_verbose (ring, "synchronizing on '%s' as participant %u",
		name, synchronize->count);
  assert (synchronize->count <= synchronize->size);

  if (synchronize->count == synchronize->size)
    {
      synchronize->count = 0;
      synchronize->function = 0;
      synchronize->name = 0;
      pthread_cond_broadcast (&synchronize->condition);
    }
  else
    {
      while (synchronize->count && synchronize->function == function)
	pthread_cond_wait (&synchronize->condition, &synchronize->mutex);
    }

  if (pthread_mutex_unlock (&synchronize->mutex))
    fatal_error ("failed to release synchronization lock during rendezvous");
}
