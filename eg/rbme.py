# x(2*i) being true means player i enters the critical region
# x(2*i+1) being true means player i has the token

(lambda n:
{'modules': [
	{'ctrl': [i*2, i*2+1],

	'init': ["T -> x"+str(i*2)+"' := F, x"+str(i*2+1)+"' := T"] if i == 0
		else ["T -> x"+str(i*2)+"' := F, x"+str(i*2+1)+"' := F"],
	'update': ["or x"+str(i*2)+" (and !x"+str(((i-1)%n)*2)+" x"+str(((i-1)%n)*2+1)+") -> x"+str(i*2)+"' := T, x"+str(i*2+1)+"' := T",
		"or x"+str(i*2)+" (and !x"+str(((i-1)%n)*2)+" x"+str(((i-1)%n)*2+1)+") -> x"+str(i*2)+"' := F, x"+str(i*2+1)+"' := T",
		"and !x"+str(i*2)+" x"+str(i*2+1)+" -> x"+str(i*2+1)+"' := F"]
	} for i in range(n) ],

'goals': ["AG AF ! x"+str(i*2) for i in range(n)],

'strategies': [
	{'ctrl': [i*2, i*2+1],
	'init': ["T -> x"+str(i*2)+"' := F, x"+str(i*2+1)+"' := T"] if i == 0
		else ["T -> x"+str(i*2)+"' := F, x"+str(i*2+1)+"' := F"],
	'update': ["and !x"+str(((i-1)%n)*2)+" x"+str(((i-1)%n)*2+1)+" -> x"+str(i*2)+"' := T, x"+str(i*2+1)+"' := T",
		"x"+str(i*2)+" -> x"+str(i*2)+"' := F, x"+str(i*2+1)+"' := T",
		"and !x"+str(i*2)+" x"+str(i*2+1)+" -> x"+str(i*2+1)+"' := F"]
	} for i in range(n) ]
})(10)
