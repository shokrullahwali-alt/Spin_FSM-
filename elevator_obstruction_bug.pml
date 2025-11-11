/* elevator_obstruction_bug.pml
   Buggy variant: allows door to transition to CLOSED even when door_obstructed == true
   This should trigger property failures for door obstruction safety.
*/

#include "elevator.pml"

/* The buggy behavior is injected by allowing door_obstructed to be ignored in Elevator.
   To keep things simple we include the base model and override the Elevator proctype.
*/

proctype Elevator()
{
  do
  ::
    /* If at target, stop and open door */
    if
    :: (floor == target) ->
        moving = false;
        door = OPEN;

    :: else ->
        /* BUG: ignore door_obstructed and close/move anyway */
        door = CLOSED;
        moving = true;
        if
        :: (floor < target) -> floor = floor + 1;
        :: (floor > target) -> floor = floor - 1;
        fi;
    fi;
  od
}
