/* elevator_obstruction_bug_full.pml
   Standalone buggy model: copy of elevator.pml with Elevator proctype modified
   to ignore door_obstructed (buggy behavior). This avoids include/override
   complexities and lets the harness run this variant directly.
*/

/* Parameters */
#define N_FLOORS 4
#define MAX_WEIGHT 10

/* Scheduling policy: define one of these at compile time */
/* #define POLICY_FIFO */
/* #define POLICY_SCAN */
/* Default to FIFO if none defined */
#ifndef POLICY_FIFO
#ifndef POLICY_SCAN
#define POLICY_FIFO
#endif
#endif

/* Types: single mtype namespace used for both modes and door symbols */
mtype = { NORMAL, FIRE, VIP, SAFE, CLOSED, OPEN };

/* Globals */
byte floor = 0;           /* current floor */
byte target = 0;          /* current objective floor */
mtype mode = NORMAL; /* current mode */
mtype door = CLOSED; /* door state */
bool moving = false;      /* elevator in motion */
bool rq[N_FLOORS];        /* floor requests (call buttons) */
bool vip_req = false;     /* VIP request active */
byte vip_dest = 0;        /* VIP destination */

/* New realism features */
bool sensor_ok = true;    /* sensor health; if false -> SAFE mode */
byte weight = 0;          /* current load */
bool door_obstructed = false; /* door blocked */

/* FIFO queue for scheduling (bounded to N_FLOORS entries) */
byte q[N_FLOORS]; /* queue contents: floor indices */
byte q_head = 0;
byte q_tail = 0;
byte q_count = 0;

/* SCAN state (used if POLICY_SCAN) */
byte scan_idx = 0;
bool scan_dir_up = true;

/* Controller: decides target and mode (priority: FIRE > VIP > NORMAL) */
proctype Controller()
{
  byte i;
  do
  ::
    /* Sensor failure -> SAFE mode (sticky) */
    if
    :: (!sensor_ok) ->
        atomic {
          mode = SAFE;
          /* choose nearest floor as target */
          if
          :: target = floor
          fi
        }

    :: else ->
        /* Emergency: if FIRE, set target to ground (0) */
        if
        :: (mode == FIRE) ->
            atomic { target = 0; }

        :: else ->
            /* VIP handling */
            if
            :: (vip_req) ->
                atomic { mode = VIP; target = vip_dest; }
            :: else ->
                /* Normal operation: scheduling policy */
                atomic {
                  mode = NORMAL;
#ifdef POLICY_FIFO
                  /* FIFO: dequeue if queue not empty */
                  if
                  :: (q_count > 0) ->
                      target = q[q_head];
                  :: else -> skip
                  fi
#endif
#ifdef POLICY_SCAN
                  /* SCAN: continue in current direction scanning for rq[] */
                  i = 0;
                  do
                  :: (i < N_FLOORS) ->
                      if
                      :: (scan_dir_up && scan_idx < N_FLOORS && rq[scan_idx]) -> target = scan_idx; break;
                      :: (!scan_dir_up && scan_idx < N_FLOORS && rq[scan_idx]) -> target = scan_idx; break;
                      :: else -> scan_idx = (scan_idx + 1) % N_FLOORS; i = i + 1;
                      fi
                  :: else -> skip; break
                  od
#endif
                }
            fi
        fi
    fi;

    /* If we are at target and stopped, service request(s) */
    if
    :: (floor == target && !moving && door == OPEN) ->
        /* clear served requests and VIP if applicable */
served:
        atomic {
          /* progress label: request served */
          if
          :: (vip_req && mode == VIP && floor == vip_dest) -> vip_req = false; mode = NORMAL;
          :: else -> skip;
          fi;
          if
          :: rq[floor] -> rq[floor] = false; /* service request */
#ifdef POLICY_FIFO
          /* If FIFO, remove from queue head if matches */
          :: (q_count > 0 && q[q_head] == floor) -> q_head = (q_head + 1) % N_FLOORS; q_count = q_count - 1;
#endif
          :: else -> skip;
          fi
        }
    :: else -> skip
    fi;

    skip;
  od
}

/* Elevator: MOVED version with BUG - ignores door_obstructed when closing and moving */
proctype Elevator()
{
  do
  ::
    /* Respect SAFE mode or sensor failure: stay stopped and open door */
    if
    :: (mode == SAFE) ->
        moving = false;
        door = OPEN;

    :: (floor == target) ->
        moving = false;
        door = OPEN;
        /* assertion safety: never move while door open */
        assert(!(moving && door == OPEN));

    :: else ->
        /* BUGGY: Attempt to close door and move even if door_obstructed is true */
        door = CLOSED;
        /* BUG: ignore door_obstructed and close/move anyway */
        if
        :: (weight > MAX_WEIGHT) -> door = OPEN; moving = false;
        :: else ->
            moving = true;
            if
            :: (floor < target) -> floor = floor + 1;
            :: (floor > target) -> floor = floor - 1;
            fi;
        fi;
    fi;
  od
}

/* Environment: generates requests, FIRE, and VIP nondeterministically
   Bounded toggling to keep state-space manageable. */
proctype Env()
{
  byte steps = 0;
  do
  :: (steps < 200) ->
      atomic {
  /* nondeterministically set a normal request and enqueue if FIFO */
  if
  :: rq[0] = true;
#ifdef POLICY_FIFO
     if
     :: (q_count < N_FLOORS) -> q[q_tail] = 0; q_tail = (q_tail + 1) % N_FLOORS; q_count = q_count + 1;
     :: else -> skip
     fi
#endif
  :: rq[1] = true;
#ifdef POLICY_FIFO
     if
     :: (q_count < N_FLOORS) -> q[q_tail] = 1; q_tail = (q_tail + 1) % N_FLOORS; q_count = q_count + 1;
     :: else -> skip
     fi
#endif
  :: (N_FLOORS > 2) ->
     rq[2] = true;
#ifdef POLICY_FIFO
     if
     :: (q_count < N_FLOORS) -> q[q_tail] = 2; q_tail = (q_tail + 1) % N_FLOORS; q_count = q_count + 1;
     :: else -> skip
     fi
#endif
  :: (N_FLOORS > 3) ->
     rq[3] = true;
#ifdef POLICY_FIFO
     if
     :: (q_count < N_FLOORS) -> q[q_tail] = 3; q_tail = (q_tail + 1) % N_FLOORS; q_count = q_count + 1;
     :: else -> skip
     fi
#endif
  :: else -> skip
  fi;

        /* nondeterministic VIP (rare) */
        if
        :: (!vip_req) -> vip_req = true; vip_dest =  ( (floor+1) % N_FLOORS )
        :: else -> skip
        fi;

  /* occasional FIRE toggle (rare) - model as nondet event */
  if
  :: (mode == FIRE) -> skip
  :: else -> skip
  fi;

        /* door obstruction may appear/disappear while door OPEN */
        if
        :: (door == OPEN) -> if :: door_obstructed = true :: door_obstructed = false fi
        :: else -> skip
        fi;

        /* weight changes only when door open (people get in/out) */
        if
        :: (door == OPEN) ->
            /* small nondeterministic changes bounded to avoid thrashing */
            if
            :: weight = weight /* no change */
            :: (weight < 255) -> weight = weight + 1
            :: (weight > 0) -> weight = weight - 1
            fi
        :: else -> skip
        fi;

        /* sensor may fail once (flip to false) but not recover in this model */
        if
        :: (!sensor_ok) -> skip
        :: else -> if :: sensor_ok = false :: skip fi
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
