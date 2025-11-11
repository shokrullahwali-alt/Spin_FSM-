never  {    /* [] !(moving && door == OPEN) */
accept_init:
T0_init:
	do
	:: (! ((moving && door == OPEN))) -> goto T0_init
	od;
}
