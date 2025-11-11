/* elevator_normal_simple_1.pml
   Tiny model to prove normal request liveness (4-floor variant)
*/

#define N_FLOORS 4

byte floor = 0;
byte target = 2;
bool rq[N_FLOORS];

proctype SimpleElevator1()
{
    /* initial request: someone calls elevator to target */
    rq[target] = true;

    do
    :: (floor == target) ->
        /* open door and service request */
        if
        :: rq[floor] ->
normal_request_served:  /* Progress: normal request served */
            rq[floor] = false;
            break;
        :: else -> break
        fi
    :: (floor < target) -> floor = floor + 1
    :: (floor > target) -> floor = floor - 1
    od
}

init { run SimpleElevator1(); }
