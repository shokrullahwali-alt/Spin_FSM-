/* elevator_normal_simple_2.pml
   Tiny model to prove normal request liveness (alternate scenario)
   Start at a higher floor and have multiple queued requests.
*/

#define N_FLOORS 4

byte floor = 3; /* start at top */
byte target1 = 1;
byte target2 = 2;
bool rq[N_FLOORS];
byte q_idx = 0;

proctype SimpleElevator2()
{
    /* two pending requests */
    rq[target1] = true;
    rq[target2] = true;

    /* service first pending request (target1) */
    do
    :: (rq[target1]) ->
        /* move towards target1 */
        if
        :: (floor < target1) -> floor = floor + 1
        :: (floor > target1) -> floor = floor - 1
        :: (floor == target1) ->
            /* service it */
normal_request_served:  /* Progress: normal request served */
            rq[target1] = false; break
        fi
    od
}

init { run SimpleElevator2(); }
