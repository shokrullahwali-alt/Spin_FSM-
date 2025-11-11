/* elevator_bug.pml
   Intentionally buggy variant: allows the door to open while moving
   (violates safety) to produce a counterexample for demonstration. */

#define N_FLOORS 4

/* single mtype namespace */
mtype = { NORMAL, FIRE, VIP, CLOSED, OPEN };

byte floor = 0; byte target = 0; mtype mode = NORMAL; mtype door = CLOSED;
bool moving = false; bool rq[N_FLOORS]; bool vip_req = false; byte vip_dest = 0;

proctype Controller() {
  byte i;
  do
  :: (mode == FIRE) ->
    /* emergency target */
    target = 0;
  :: (vip_req) ->
    mode = VIP;
    target = vip_dest;
  :: else ->
    mode = NORMAL;
    i = 0;
    do
    :: (i < N_FLOORS) ->
     if
     :: rq[i] ->
      target = i;
      break;
     :: else ->
      i = i + 1;
     fi
    :: else -> break
    od
  od
}

proctype Elevator() {
  do
  :: (floor == target) ->
    /* BUG: open door before stopping (moving may still be true) */
    door = OPEN;
    moving = false;
  :: else ->
    door = CLOSED;
    moving = true;
    if
    :: (floor < target) -> floor = floor + 1;
    :: (floor > target) -> floor = floor - 1;
    fi
  od
}

proctype Env() {
  byte steps = 0;
  do
  :: (steps < 50) ->
    rq[0] = true;
    rq[1] = true;
    steps = steps + 1;
  :: else -> break
  od
}

init {
  byte i = 0;
  do
  :: (i < N_FLOORS) -> rq[i] = false; i = i + 1;
  :: else -> break
  od;
  run Controller();
  run Elevator();
  run Env();
}
