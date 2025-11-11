/* elevator_req0_witness.pml
   Minimal witness: starts with door open at floor 0 and rq[0]=true; Monitor prints and asserts.
*/

#define N_FLOORS 4

mtype = { NORMAL, FIRE, VIP, SAFE, CLOSED, OPEN };

byte floor = 0;
mtype door = OPEN;
bool moving = false;
bool rq[N_FLOORS];

proctype Monitor()
{
  do
  :: (floor == 0 && !moving && door == OPEN && rq[0]) ->
      rq[0] = false; printf("LABEL req0_served fired\n"); assert(false);
  :: else -> break;
  od
}

init {
  byte i;
  i = 0;
  do :: (i < N_FLOORS) -> rq[i] = false; i = i + 1; :: else -> break; od;
  rq[0] = true;
  run Monitor();
}
