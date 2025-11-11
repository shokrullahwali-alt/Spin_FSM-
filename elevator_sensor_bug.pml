/* elevator_sensor_bug.pml
   Buggy variant: after sensor failure, controller still allows movement (i.e., fails to enter SAFE)
*/

#include "elevator.pml"

proctype Controller()
{
  byte i;
  do
  ::
    /* BUG: ignore sensor_ok and do not enter SAFE mode */
    if
    :: (mode == FIRE) -> atomic { target = 0; }
    :: else ->
        if
        :: (vip_req) -> atomic { mode = VIP; target = vip_dest; }
        :: else -> atomic { mode = NORMAL; i = 0; do :: (i < N_FLOORS) -> if :: rq[i] -> target = i; break :: else -> i = i + 1 fi :: else -> skip; break od }
        fi
    fi;

    if
    :: (floor == target && !moving && door == OPEN) -> atomic { if :: (vip_req && mode == VIP && floor == vip_dest) -> vip_req = false; mode = NORMAL; :: else -> skip fi; if :: rq[floor] -> rq[floor] = false :: else -> skip fi }
    :: else -> skip
    fi;

    skip;
  od
}
