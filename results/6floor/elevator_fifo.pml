#define POLICY_FIFO
/*
  elevator_6floor.pml
  Smart Elevator model: 6 floors (0..5), modes NORMAL,FIRE,VIP,SAFE
  Includes: weight/overload, door obstruction, sensor failure
  Extended from 4-floor model for larger building scenarios.
*/

/* Parameters */
#define N_FLOORS 6
#define MAX_WEIGHT 10

/* Scheduling policy: define one of these at compile time */
/* #define POLICY_FIFO */
/* #define POLICY_SCAN */

mtype = { NORMAL, FIRE, VIP, SAFE, CLOSED, OPEN };

/* System state */
byte floor = 0;           /* current floor */
byte target = 0;          /* target floor (decided by Controller) */
mtype mode = NORMAL;      /* operating mode */
mtype door = CLOSED;      /* door state */
bool moving = false;      /* is elevator moving */

/* Requests */
bool rq[N_FLOORS];        /* floor requests (0..5) */
bool vip_req = false;     /* VIP request pending */
byte vip_dest = 0;        /* VIP destination floor */

/* FIFO queue state (for POLICY_FIFO) */
byte q[N_FLOORS];         /* queue of floors */
byte q_head = 0;
byte q_tail = 0;
byte q_count = 0;

/* SCAN state (for POLICY_SCAN) */
byte scan_idx = 0;
bool scan_dir_up = true;

/* Realism features */
bool sensor_ok = true;    /* sensor health; if false -> SAFE mode */
byte weight = 0;          /* current load */
bool door_obstructed = false; /* door blocked */

/* Controller: decides target and mode (priority: FIRE > SAFE > VIP > NORMAL) */
proctype Controller()
{
  byte i;
  do
  ::
    /* Priority order: FIRE > SAFE > VIP > NORMAL */
    /* Emergency FIRE mode: absolute highest priority */
    if
    :: (mode == FIRE) ->
        atomic { target = 0; }

    :: else ->
        /* Sensor failure -> SAFE mode (sticky), but only if not in FIRE */
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
          /* Clear FIRE mode if at ground floor - mark as progress */
          if
          :: (mode == FIRE && floor == 0) ->
fire_goal_reached:  /* Progress: FIRE emergency goal achieved */
              mode = NORMAL;
          :: else -> skip;
          fi;
          /* Clear VIP mode if VIP request served */
          if
          :: (vip_req && mode == VIP && floor == vip_dest) ->
vip_goal_reached:  /* Progress: VIP request goal achieved */
              vip_req = false; mode = NORMAL;
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

/* Elevator: moves towards target, enforces door/moving invariants */
proctype Elevator()
{
  do
  ::
    /* Safety assertion: check at top of loop */
    assert(!(moving && door == OPEN));

    /* Respect SAFE mode or sensor failure: stay stopped and open door */
    if
    :: (mode == SAFE) ->
        atomic {
          moving = false;
          door = OPEN;
        }

    :: (floor == target) ->
        atomic {
          moving = false;
          door = OPEN;
        }

    :: else ->
    /* Attempt to close door and (atomically) decide whether to move.
       Make the close/check/move sequence atomic to avoid interleavings
       that could set door=open while moving==true. */
    atomic {
      door = CLOSED;
      if
      :: (door_obstructed) ->
         /* re-open immediately */
         door = OPEN;
         moving = false;
      :: else ->
         /* If overloaded, do not move; keep door open instead */
         if
         :: (weight > MAX_WEIGHT) -> door = OPEN; moving = false;
         :: else ->
          /* start moving only if door remained CLOSED; otherwise stay stopped */
          if
          :: (door == CLOSED) ->
            moving = true;
            if
            :: (floor < target) -> floor = floor + 1;
            :: (floor > target) -> floor = floor - 1;
            fi
          :: else -> moving = false
          fi;
         fi;
      fi;
    }
    fi;

    /* Safety assertion: check at bottom of loop */
    assert(!(moving && door == OPEN));
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
  :: (N_FLOORS > 4) ->
     rq[4] = true;
#ifdef POLICY_FIFO
     if
     :: (q_count < N_FLOORS) -> q[q_tail] = 4; q_tail = (q_tail + 1) % N_FLOORS; q_count = q_count + 1;
     :: else -> skip
     fi
#endif
  :: (N_FLOORS > 5) ->
     rq[5] = true;
#ifdef POLICY_FIFO
     if
     :: (q_count < N_FLOORS) -> q[q_tail] = 5; q_tail = (q_tail + 1) % N_FLOORS; q_count = q_count + 1;
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
  /* FIRE mode is sticky once set (until serviced at ground floor) */
  if
  :: (mode != FIRE && mode != SAFE) -> mode = FIRE  /* trigger FIRE mode */
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

/* Monitor: continuously check invariants (optional; assertions also check) */
proctype Monitor()
{
  do
  ::
    /* If moving, door must be closed */
    assert(!(moving && door == OPEN));
  od
}

init {
  byte i;
  atomic {
    /* initialize request array */
    i = 0;
    do
    :: (i < N_FLOORS) -> rq[i] = false; i = i + 1;
    :: else -> break
    od;

    run Controller();
    run Elevator();
    run Env();
    run Monitor();
  }
}
