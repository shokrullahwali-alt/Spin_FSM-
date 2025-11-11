/* Simplified elevator model for FIRE mode liveness testing */
#define N_FLOORS 4

mtype = { NORMAL, FIRE, CLOSED, OPEN };

/* State */
byte floor = 2;       /* Start at floor 2 to test movement to ground */
byte target = 2;
mtype mode = NORMAL;
mtype door = CLOSED;
bool moving = false;

/* Simple Controller: FIRE priority */
proctype Controller()
{
  do
  ::
    if
    :: (mode == FIRE) ->
        atomic { target = 0; }  /* Emergency: go to ground */
    :: else ->
        /* Normal: stay at current floor */
        atomic { target = floor; }
    fi;

    /* Clear FIRE mode once goal is reached - mark as progress */
    if
    :: (mode == FIRE && floor == 0 && door == OPEN && !moving) ->
fire_goal_reached:  /* Progress label: FIRE goal achieved */
        atomic { mode = NORMAL; }
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

/* Simple Env: trigger FIRE once */
proctype Env()
{
  /* Wait a bit, then trigger FIRE */
  skip; skip; skip;
  atomic { mode = FIRE; }
  /* Exit - done setting FIRE */
}

init {
  atomic {
    run Controller();
    run Elevator();
    run Env();
  }
}
