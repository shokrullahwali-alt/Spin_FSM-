/* elevator_normal_det_4.pml
   Deterministic test: 4-floor model that sequentially services all floor requests
   This is used to provide a fast conclusive check for per-request progress labels.
*/

#define N_FLOORS 4

byte floor = 0;
bool rq[N_FLOORS];

init {
    /* set a pending request on every floor */
    rq[0] = true; rq[1] = true; rq[2] = true; rq[3] = true;

    /* deterministically visit floors in order and service them */
    floor = 0;
    if
    :: (rq[0]) -> req0_served: rq[0] = false;
    :: else -> skip;
    fi;

    floor = 1;
    if
    :: (rq[1]) -> req1_served: rq[1] = false;
    :: else -> skip;
    fi;

    floor = 2;
    if
    :: (rq[2]) -> req2_served: rq[2] = false;
    :: else -> skip;
    fi;

    floor = 3;
    if
    :: (rq[3]) -> req3_served: rq[3] = false;
    :: else -> skip;
    fi;

}
