	switch (t->back) {
	default: Uerror("bad return move");
	case  0: goto R999; /* nothing to undo */

		 /* PROC :init: */

	case 3: // STATE 1
		;
		((P1 *)_this)->i = trpt->bup.oval;
		;
		goto R999;
;
		;
		
	case 5: // STATE 3
		;
		now.rq[ Index(((P1 *)_this)->i, 4) ] = trpt->bup.oval;
		;
		goto R999;

	case 6: // STATE 4
		;
		((P1 *)_this)->i = trpt->bup.oval;
		;
		goto R999;

	case 7: // STATE 10
		;
		now.rq[0] = trpt->bup.oval;
		;
		goto R999;

	case 8: // STATE 11
		;
		;
		delproc(0, now._nr_pr-1);
		;
		goto R999;

	case 9: // STATE 12
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* PROC Monitor */
;
		;
		
	case 11: // STATE 2
		;
		now.rq[0] = trpt->bup.oval;
		;
		goto R999;
;
		
	case 12: // STATE 3
		goto R999;

	case 13: // STATE 10
		;
		p_restor(II);
		;
		;
		goto R999;
	}

