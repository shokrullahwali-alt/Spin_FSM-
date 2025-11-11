never  {    /* [] ((mode == 1) -> <> ((floor == 0) && (door == 3) && (!moving))) */
T0_init:
	do
	:: ((! ((mode == 1)) || ((floor == 0) && (door == 3) && (!moving)))) -> goto accept_S20
	:: (1) -> goto T0_S27
	od;
accept_S20:
	do
	:: ((! ((mode == 1)) || ((floor == 0) && (door == 3) && (!moving)))) -> goto T0_init
	:: (1) -> goto T0_S27
	od;
accept_S27:
	do
	:: (((floor == 0) && (door == 3) && (!moving))) -> goto T0_init
	:: (1) -> goto T0_S27
	od;
T0_S27:
	do
	:: (((floor == 0) && (door == 3) && (!moving))) -> goto accept_S20
	:: (1) -> goto T0_S27
	:: (((floor == 0) && (door == 3) && (!moving))) -> goto accept_S27
	od;
}
