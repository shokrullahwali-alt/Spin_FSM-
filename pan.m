#define rand	pan_rand
#define pthread_equal(a,b)	((a)==(b))
#if defined(HAS_CODE) && defined(VERBOSE)
	#ifdef BFS_PAR
		bfs_printf("Pr: %d Tr: %d\n", II, t->forw);
	#else
		cpu_printf("Pr: %d Tr: %d\n", II, t->forw);
	#endif
#endif
	switch (t->forw) {
	default: Uerror("bad forward move");
	case 0:	/* if without executable clauses */
		continue;
	case 1: /* generic 'goto' or 'skip' */
		IfNotBlocked
		_m = 3; goto P999;
	case 2: /* generic 'else' */
		IfNotBlocked
		if (trpt->o_pm&1) continue;
		_m = 3; goto P999;

		 /* PROC :init: */
	case 3: // STATE 1 - elevator_req0_witness.pml:25 - [i = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[1][1] = 1;
		(trpt+1)->bup.oval = ((int)((P1 *)_this)->i);
		((P1 *)_this)->i = 0;
#ifdef VAR_RANGES
		logval(":init::i", ((int)((P1 *)_this)->i));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 4: // STATE 2 - elevator_req0_witness.pml:26 - [((i<4))] (0:0:0 - 1)
		IfNotBlocked
		reached[1][2] = 1;
		if (!((((int)((P1 *)_this)->i)<4)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 5: // STATE 3 - elevator_req0_witness.pml:26 - [rq[i] = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[1][3] = 1;
		(trpt+1)->bup.oval = ((int)now.rq[ Index(((int)((P1 *)_this)->i), 4) ]);
		now.rq[ Index(((P1 *)_this)->i, 4) ] = 0;
#ifdef VAR_RANGES
		logval("rq[:init::i]", ((int)now.rq[ Index(((int)((P1 *)_this)->i), 4) ]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 6: // STATE 4 - elevator_req0_witness.pml:26 - [i = (i+1)] (0:0:1 - 1)
		IfNotBlocked
		reached[1][4] = 1;
		(trpt+1)->bup.oval = ((int)((P1 *)_this)->i);
		((P1 *)_this)->i = (((int)((P1 *)_this)->i)+1);
#ifdef VAR_RANGES
		logval(":init::i", ((int)((P1 *)_this)->i));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 7: // STATE 10 - elevator_req0_witness.pml:27 - [rq[0] = 1] (0:0:1 - 3)
		IfNotBlocked
		reached[1][10] = 1;
		(trpt+1)->bup.oval = ((int)now.rq[0]);
		now.rq[0] = 1;
#ifdef VAR_RANGES
		logval("rq[0]", ((int)now.rq[0]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 8: // STATE 11 - elevator_req0_witness.pml:28 - [(run Monitor())] (0:0:0 - 1)
		IfNotBlocked
		reached[1][11] = 1;
		if (!(addproc(II, 1, 0)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 9: // STATE 12 - elevator_req0_witness.pml:29 - [-end-] (0:0:0 - 1)
		IfNotBlocked
		reached[1][12] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* PROC Monitor */
	case 10: // STATE 1 - elevator_req0_witness.pml:17 - [(((((floor==0)&&!(moving))&&(door==OPEN))&&rq[0]))] (0:0:0 - 1)
		IfNotBlocked
		reached[0][1] = 1;
		if (!(((((((int)now.floor)==0)&& !(((int)now.moving)))&&(now.door==1))&&((int)now.rq[0]))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 11: // STATE 2 - elevator_req0_witness.pml:18 - [rq[0] = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[0][2] = 1;
		(trpt+1)->bup.oval = ((int)now.rq[0]);
		now.rq[0] = 0;
#ifdef VAR_RANGES
		logval("rq[0]", ((int)now.rq[0]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 12: // STATE 3 - elevator_req0_witness.pml:18 - [printf('LABEL req0_served fired\\n')] (0:7:0 - 1)
		IfNotBlocked
		reached[0][3] = 1;
		Printf("LABEL req0_served fired\n");
		/* merge: assert(0)(7, 4, 7) */
		reached[0][4] = 1;
		spin_assert(0, "0", II, tt, t);
		/* merge: .(goto)(0, 8, 7) */
		reached[0][8] = 1;
		;
		_m = 3; goto P999; /* 2 */
	case 13: // STATE 10 - elevator_req0_witness.pml:21 - [-end-] (0:0:0 - 3)
		IfNotBlocked
		reached[0][10] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */
	case  _T5:	/* np_ */
		if (!((!(trpt->o_pm&4) && !(trpt->tau&128))))
			continue;
		/* else fall through */
	case  _T2:	/* true */
		_m = 3; goto P999;
#undef rand
	}

