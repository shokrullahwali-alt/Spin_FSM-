/* elevator_normal_det_6.pml
   Deterministic test: 6-floor model that sequentially services all floor requests
*/

#define N_FLOORS 6

byte floor = 0;
bool rq[N_FLOORS];

init {
    /* set a pending request on every floor */
    rq[0] = true; rq[1] = true; rq[2] = true; rq[3] = true; rq[4] = true; rq[5] = true;

    floor = 0; if :: (rq[0]) -> req0_served: rq[0] = false; :: else -> skip; fi;
    floor = 1; if :: (rq[1]) -> req1_served: rq[1] = false; :: else -> skip; fi;
    floor = 2; if :: (rq[2]) -> req2_served: rq[2] = false; :: else -> skip; fi;
    floor = 3; if :: (rq[3]) -> req3_served: rq[3] = false; :: else -> skip; fi;
    floor = 4; if :: (rq[4]) -> req4_served: rq[4] = false; :: else -> skip; fi;
    floor = 5; if :: (rq[5]) -> req5_served: rq[5] = false; :: else -> skip; fi;
}
