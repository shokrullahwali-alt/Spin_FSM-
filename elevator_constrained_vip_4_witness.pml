/* elevator_constrained_vip_4_witness.pml
   Witness run for VIP: stops on first occurrence of VIP serving and prints a LABEL line.
*/

#define N_FLOORS 4
#define MAX_WEIGHT 10
#define POLICY_FIFO

mtype = { NORMAL, FIRE, VIP, SAFE, CLOSED, OPEN };

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

proctype Controller()
{
  byte i;
  do
  :: atomic {
      if
      :: (mode == FIRE) -> target = 0;
      :: else ->
          if
          :: (!sensor_ok) -> mode = SAFE; target = floor;
          :: else ->
              if
              :: (vip_req) -> mode = VIP; target = vip_dest;
              :: else ->
                  mode = NORMAL;
                  i = 0;
                  do
                  :: (i < N_FLOORS) ->
                      if
                      :: (rq[i]) -> target = i; break;
                      :: else -> i = i + 1;
                      fi
                  :: else -> break
                  od
              fi
          fi
      fi
    }
  od
}

proctype Elevator()
{
  do
  ::
    assert(!(moving && door == OPEN));

    if
    :: (mode == SAFE) -> atomic { moving = false; door = OPEN; }
    :: (floor == target) -> atomic { moving = false; door = OPEN; }
    :: else ->
      atomic {
        door = CLOSED;
        if
        :: (door_obstructed) -> door = OPEN; moving = false;
        :: else ->
            if
            :: (weight > MAX_WEIGHT) -> door = OPEN; moving = false;
            :: else ->
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

    assert(!(moving && door == OPEN));
  od
}

init {
  byte i;
  atomic {
    /* initialize requests: set all normal requests to false (only VIP present) */
    i = 0;
    do :: (i < N_FLOORS) -> rq[i] = false; i = i + 1; :: else -> break; od;
    floor = 0; target = 0; mode = NORMAL; door = CLOSED; moving = false;
    /* set a VIP request to floor 2 */
    vip_req = true; vip_dest = 2;
  }
  run Controller();
  run Elevator();
}

proctype Monitor()
{
  do
  :: (vip_req && floor == vip_dest && !moving && door == OPEN) ->
      vip_req = false; vip_goal_reached: printf("LABEL vip_goal_reached fired\n"); assert(false);
  :: (floor == 0 && !moving && door == OPEN && rq[0]) ->
      rq[0] = false; req0_served: printf("LABEL req0_served fired\n"); assert(false);
  :: (floor == 1 && !moving && door == OPEN && rq[1]) ->
      rq[1] = false; req1_served: printf("LABEL req1_served fired\n"); assert(false);
  :: (floor == 2 && !moving && door == OPEN && rq[2]) ->
      rq[2] = false; req2_served: printf("LABEL req2_served fired\n"); assert(false);
  :: (floor == 3 && !moving && door == OPEN && rq[3]) ->
      rq[3] = false; req3_served: printf("LABEL req3_served fired\n"); assert(false);
  :: else -> skip;
  od
}

init { run Monitor(); }
