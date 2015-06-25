# This module implements the translation from a list of modules to a Kripke structure.
# The unfoldings of the Kripke structure are in strong correspondance with the outcome of the game.
# Nodes of the structure are valuations of the variables controlled by the modules.
# There is an edge between nodes u and v whenever there is a joint guarded command J that is enabled at u, and exec(J, u) = v

from rm import *

from networkx import *
from mrwaffles.checker import *
from mrwaffles.ctl import *


import pickle


# Nodes need to be labeled with hashable types, so we convert valuation lists into ints 
#	such that the i-th digit of lab(v) is 1 iff v maps variable i to true.

# maps valuations to int labels
def lab(v):
	n = 0
	for x in v:
		n += 2**x
	return n

# maps int labels to valuations
def lab2val(n):
	x = 0
	v = []
	while n > 0:
		if n % 2 == 1:
			v.append(x)
		n = n/2
		x += 1
	return sorted(v)

# translates a list of modules into a mrwaffles PredicatedGraph
def Arena2Kripke(modules):
	A = PredicatedGraph()
	S0 = set()
	S = set()

	for J in jointEnabled_init(modules):
		v = jointExe(modules, J, [])
		vlab = lab(v)

		if vlab not in S:
			S0.add(vlab)
			S.add(vlab)
			A.add_node(vlab)

			for x in v:
				A.add_predicate(vlab, 'x'+str(x))
    
	X = set()
	while X != S:
		X = copy.copy(S)
		for vlab in X:
			v = lab2val(vlab)

			for J in jointEnabled(modules, v):
				w = jointExe(modules, J, v)
				wlab = lab(w)

				if not wlab in S:
					S.add(wlab)
					A.add_node(wlab)
					for x in w:
						A.add_predicate(wlab, 'x'+str(x))
    
	for vlab in S:
		for wlab in S:
			v = lab2val(vlab)
			w = lab2val(wlab)
			for J in jointEnabled(modules, v):
				if w == jointExe(modules, J, v):
					A.add_edge(vlab, wlab)
					break

	return (A, S0)

# return true iff Kripke structure A with starting states S0 satisfies the formula goal
def entails(A, S0, goal):
	states = A.check(goal)

	for s in S0:
		if not s in states:
			return False
	return True

