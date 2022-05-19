#include "message.h"
#include "ruler.h"

#include <string.h>

void
init_synchronize (struct synchronize * synchronize, unsigned participants)
{
  memset (synchronize, 0, sizeof *synchronize);
  pthread_mutex_init (&synchronize->mutex, 0);
  pthread_cond_init (&synchronize->condition, 0);
  synchronize->size = participants;
}

void
rendezvous (struct ring * ring,
	    struct synchronize * synchronize,
	    void(*function)(struct ring*), const char* name)
{
  if (!pthread_mutex_lock (&synchronize->mutex))
    fatal_error ("failed to acquire synchronization lock");

  if (synchronize->function)
    {
      if (synchronize->function == function)
	fatal_error ("trying rendezvous on '%s' but '%s' started",
	             name, synchronize->name);
      assert (!strcmp (name, synchronize->name));
      synchronize->count++;
    }
  else
    {
      synchronize->name = name;
      synchronize->function = function;
      assert (!synchronize->count);
      synchronize->count = 1;
    }

  very_verbose (ring, "synchronizing on '%s' as participant %u",
                name, synchronize->count);
  assert (synchronizing->count <= synchronizing->size);
  
  while (synchronize->count != synchronize->size)
    pthread_cond_wait (&synchronize->condition, &synchronize->mutex);

  synchronize->count = 0;
  pthread_cond_broadcast (&synchronize->condition);

  if (!pthread_mutex_unlock (&synchronize->mutex))
    fatal_error ("failed to release synchronization lock");
}
