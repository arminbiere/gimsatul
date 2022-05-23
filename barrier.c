#include "message.h"
#include "ruler.h"

#include <string.h>

void
init_barrier (struct barrier *barrier, const char * name, unsigned size)
{
  barrier->name = name;
  barrier->size = size;
  assert (!barrier->disabled);
  if (size < 2)
    return;
  pthread_mutex_init (&barrier->mutex, 0);
  pthread_cond_init (&barrier->condition, 0);
}

void
abort_waiting_and_disable_barrier (struct barrier * barrier)
{
  if (barrier->size < 2)
    return;
  if (pthread_mutex_lock (&barrier->mutex))
    fatal_error ("failed to acquire barrier lock to abort waiting");
  if (!barrier->disabled)
    {
      very_verbose (0, "disabling %s barrier", barrier->name);
      barrier->disabled = true;
      if (barrier->waiting)
	{
	  very_verbose (0, "aborting %u waiting threads on %s barrier",
	                barrier->waiting, barrier->name);
	  barrier->waiting = 0;
	  barrier->current ^= 1;
	  pthread_cond_broadcast (&barrier->condition);
	}
    }
  if (pthread_mutex_unlock (&barrier->mutex))
    fatal_error ("failed to release barrier lock to abort waiting");
}

void
rendezvous (struct barrier * barrier, struct ring *ring)
{
  if (barrier->size < 2)
    return;
#ifndef NFASTPATH
  if (barrier->disabled)
    return;
#endif
  if (pthread_mutex_lock (&barrier->mutex))
    fatal_error ("failed to acquire barrier lock during rendezvous");

  if (!barrier->disabled)
    {
      assert (barrier->waiting < barrier->size);
      barrier->waiting++;
      very_verbose (ring, "entered barrier on '%s' (%u waiting)",
		    barrier->name, barrier->waiting);
     
      bool current = barrier->current;
      if (barrier->waiting == barrier->size)
	{
	  barrier->waiting = 0;
	  barrier->current = !current;
	  pthread_cond_broadcast (&barrier->condition);
	}
      else
	while (!barrier->disabled && current == barrier->current)
	  pthread_cond_wait (&barrier->condition, &barrier->mutex);

      very_verbose (ring, "leaving barrier on '%s'", barrier->name);
    }

  if (pthread_mutex_unlock (&barrier->mutex))
    fatal_error ("failed to release barrier lock during rendezvous");
}
