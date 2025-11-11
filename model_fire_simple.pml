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

    /* Clear FIRE mode once goal is reached */
    if
    :: (mode == FIRE && floor == 0 && door == OPEN && !moving) ->
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
  mode = FIRE;
  /* Exit - done setting FIRE */
}

init {
  atomic {
    run Controller();
    run Elevator();
    run Env();
  }
}
never  {    /* [] ((mode == 1) -> <> ((floor == 0) && (door == 3) && (!moving))) */
T0_init:
	do
	:: ((! ((mode == 1)) || ((floor == 0) && (door == 3) && (!moving)))) -> goto accept_S20
	:: (1) -> goto T0_S27
	od;
accept_S20:
	do
	:: ((! ((mode == 1)) || ((floor == 0) && (door == 3) && (!moving)))) -> goto T0_init
	:: (1) -> goto T0_S27
	od;
accept_S27:
	do
	:: (((floor == 0) && (door == 3) && (!moving))) -> goto T0_init
	:: (1) -> goto T0_S27
	od;
T0_S27:
	do
	:: (((floor == 0) && (door == 3) && (!moving))) -> goto accept_S20
	:: (1) -> goto T0_S27
	:: (((floor == 0) && (door == 3) && (!moving))) -> goto accept_S27
	od;
}
