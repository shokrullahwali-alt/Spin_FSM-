/* elevator_overload_bug.pml
   Buggy variant: allows movement while weight > MAX_WEIGHT
*/

#include "elevator.pml"

/* Override Elevator to ignore overload check */
proctype Elevator()
{
  do
  ::
    if
    :: (floor == target) ->
        moving = false; door = OPEN;
    :: else ->
        door = CLOSED;
        /* BUG: move regardless of weight */
        moving = true;
        if
        :: (floor < target) -> floor = floor + 1;
        :: (floor > target) -> floor = floor - 1;
        fi;
    fi;
  od
}
