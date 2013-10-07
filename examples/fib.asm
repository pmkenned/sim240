		ldi		r0, $1
		ldi		r1, $1
loop	add		r0, r1
		add		r1, r0
		cmi		r0, $100
		brn		loop
		stop
