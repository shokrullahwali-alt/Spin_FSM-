/* Simplified elevator model for VIP liveness testing */
#define N_FLOORS 4

mtype = { NORMAL, VIP, CLOSED, OPEN };

/* State */
byte floor = 1;       /* Start at floor 1 */
byte target = 1;
mtype mode = NORMAL;
mtype door = CLOSED;
bool moving = false;
bool vip_req = false;
byte vip_dest = 3;    /* VIP wants floor 3 */

/* Simple Controller: VIP priority */
proctype Controller()
{
  do
  ::
    if
    :: (vip_req) ->
        atomic { mode = VIP; target = vip_dest; }
    :: else ->
        /* Normal: stay at current floor */
        atomic { mode = NORMAL; target = floor; }
    fi;

    /* Clear VIP mode once goal is reached - mark as progress */
    if
    :: (vip_req && mode == VIP && floor == vip_dest && door == OPEN && !moving) ->
vip_goal_reached:  /* Progress label: VIP goal achieved */
        atomic { vip_req = false; mode = NORMAL; }
    :: else -> skip
    fi;
  od
}

/* Elevator: move and manage door */
proctype Elevator()
{
  do
  ::
    assert(!(moving && door == OPEN));

    if
    :: (floor == target) ->
        atomic { moving = false; door = OPEN; }
    :: else ->
        atomic {
          door = CLOSED;
          moving = true;
          if
          :: (floor < target) -> floor = floor + 1;
          :: (floor > target) -> floor = floor - 1;
          fi;
        }
    fi;

    assert(!(moving && door == OPEN));
  od
}

/* Simple Env: set VIP request once */
proctype Env()
{
  /* Wait a bit, then set VIP request */
  skip; skip; skip;
  atomic { vip_req = true; }
  /* Exit - done setting VIP */
}

init {
  atomic {
    run Controller();
    run Elevator();
    run Env();
  }
}
