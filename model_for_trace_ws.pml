/*
  elevator.pml
  Smart Elevator model (FULL): 4 floors (0..3), modes NORMAL,FIRE,VIP
  Clean, commented Promela model suitable for SPIN verification.

  To run MVP (2-floor) tests, the provided `run_spin.sh` will create a
  temporary MVP model by replacing the N_FLOORS define. You can also edit
  the #define below to 2 and re-run spin manually.
*/

#define N_FLOORS 2

/* Types: single mtype namespace containing both modes and door symbols. */
mtype = { NORMAL, FIRE, VIP, CLOSED, OPEN };

/* Globals */
byte floor = 0;           /* current floor */
byte target = 0;          /* current objective floor */
/* Note: Promela has a single mtype namespace. We declare mode and door
  as variables of type mtype and use the symbols above. */
mtype mode = NORMAL;      /* current mode */
mtype door = CLOSED;       /* door state */
bool moving = false;      /* elevator in motion */
bool rq[N_FLOORS];        /* floor requests (call buttons) */
bool vip_req = false;     /* VIP request active */
byte vip_dest = 0;        /* VIP destination */

/* Controller: decides target and mode (priority: FIRE > VIP > NORMAL) */
proctype Controller()
{
  byte i;
  do
  ::
    /* Emergency: if FIRE, set target to ground (0) */
    if
    :: (mode == FIRE) ->
        atomic {
          target = 0;
        }

    :: else ->
        /* VIP handling */
        if
        :: (vip_req) ->
            atomic {
              mode = VIP;
              target = vip_dest; /* non-stop: controller sets target directly */
            }
        :: else ->
            /* Normal operation: pick next pending request (scan 0..N_FLOORS-1) */
            atomic {
              mode = NORMAL;
              i = 0;
              do
              :: (i < N_FLOORS) ->
                  if
                  :: rq[i] -> target = i; break;
                  :: else -> i = i + 1;
                  fi
              :: else -> skip; break
              od
            }
        fi
    fi;

    /* If we are at target and stopped, service request(s) */
    if
    :: (floor == target && !moving && door == OPEN) ->
        /* clear served requests and VIP if applicable */
        atomic {
          if
          :: (vip_req && mode == VIP && floor == vip_dest) -> vip_req = false; mode = NORMAL;
          :: else -> skip;
          fi;
          if
          :: rq[floor] -> rq[floor] = false; /* progress: this services request */
          :: else -> skip;
          fi
        }
    :: else -> skip
    fi;

    /* small nondeterministic delay to interleave with Elevator/Env */
    skip;
  od
}

/* Elevator: moves towards target, enforces door/moving invariants */
proctype Elevator()
{
  do
  ::
    /* If at target, stop and open door */
    if
    :: (floor == target) ->
        moving = false;
        door = OPEN;
        /* assertion safety: never move while door open */
        assert(!(moving && door == OPEN));

    :: else ->
        /* Close door and move one floor toward target. Make close/check/move
           atomic to avoid interleavings that could leave door open while
           moving==true. */
        atomic {
          door = CLOSED;
          moving = true;
          if
          :: (floor < target) -> floor = floor + 1;
          :: (floor > target) -> floor = floor - 1;
          fi;
        }
        /* after move, loop will check if at target */
    fi;
  od
}

/* Environment: generates requests, FIRE, and VIP nondeterministically
   Bounded toggling to keep state-space manageable. */
proctype Env()
{
  byte steps = 0;
  do
  :: (steps < 100) ->
      atomic {
        /* nondeterministically set a normal request */
        if
        :: rq[0] = true
        :: rq[1] = true
        :: (N_FLOORS > 2) -> rq[2] = true
        :: (N_FLOORS > 3) -> rq[3] = true
        :: else -> skip
        fi;

        /* nondeterministic VIP */
        if
        :: (!vip_req) -> vip_req = true; vip_dest =  ( (floor+1) % N_FLOORS )
        :: else -> skip
        fi;

        /* occasional FIRE toggle (rare) */
        if
        :: mode = FIRE
        :: else -> skip
        fi;

        steps = steps + 1;
      }
  :: else -> break
  od;
}

/* init: compose system */
init {
  atomic {
    /* initialize requests */
    byte i;
    i = 0;
    do :: (i < N_FLOORS) -> rq[i] = false; i = i + 1; :: else -> break; od;
    floor = 0; target = 0; mode = NORMAL; door = CLOSED; moving = false;
    vip_req = false; vip_dest = 0;
  }
  run Controller();
  run Elevator();
  run Env();
}
never  {    /* [] !(moving && door == OPEN) */
accept_init:
T0_init:
	do
	:: (! ((moving && door == OPEN))) -> goto T0_init
	od;
}
