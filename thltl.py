# This module implements the translation from a list of modules to the corresponding CTL theory.
# The Kripke structures that satisfy the theory are exactly those whose tree unfoldings correspond to the arena's.

from pl import *
from rm import *

import subprocess
import math


### helper functions for indexed formulae

# builds the string for the AND of a set of formulae
def AND(fs):
	if not fs:
		return "T"
	else:
		s = ""
		for f in fs:
			s += "&"+f
		return s[1:]

def OR(fs):
	if not fs:
		return "~T"
	else:
		s = ""
		for f in fs:
			s += "| ("+f+")"
		return "("+s[1:]+")"

# builds the string for the IFF of a set of formulae
def IFF(fs):
	s = ""
	for i in range(len(fs)-1):
		s += "&("+fs[i]+"->"+fs[i+1]+")"
		s += "&("+fs[i+1]+"->"+fs[i]+")"
	return s[1:]

# builds the string for the predicate "exactly one of fs holds"
def X_ONE(fs):
	s = ""
	for i in range(len(fs)):
		s += "|("+fs[i]
		for j in range(len(fs)):
			if i != j:
				s += "&~("+fs[j]+")"
		s += ")"
	return "("+s[1:]+")"



### machinery for handling CTLSAT atoms
# (CTLSAT can only parse single characters as atoms)

# characters reserved by the CTLSAT parser, not to be used as atoms
notAtoms = ['p', 'T','B','S','N','$',')','(','>','U','^','v','A','E','C','D','H','I','J','K','~']

# characters to be used as atoms
atoms = ['a', 'b', 'c', 'd']

Ngc = 0 # number of extra variables needed for the guarded commands
# this is initialised when calling the function Th

# maps variables to ascii characters to be parsed by CTLSAT
def var2chr(n):
	assert(n < len(atoms)-Ngc) # asserts we haven't ran out of characters for atoms
	return atoms[n]

# maps guarded commands to a characteristic formula to be parsed by CTLSAT
def gc2ctl(n):
	return atoms[len(atoms)-Ngc+n]


### translations from PL and CTL formulae to CTLSAT syntax

# translates PL instances into strings to be input by CTLSAT
# used for guards and for Boolean values in update commands
def pl2ctl(f):
	if f.type == "T":
		return "T"
	elif f.type == "F":
		return "(~T)"
	elif f.type == "Var":
		return var2chr(f.n)
	elif f.type == "Not":
		return "(~"+pl2ctl(f.p)+")"
	elif f.type == "Or":
		return "("+pl2ctl(f.p)+"|"+pl2ctl(f.q)+")"
	elif f.type == "And":
		return "("+pl2ctl(f.p)+"&"+pl2ctl(f.q)+")"

# translates the abstract syntax tree of a formula into a string to be input by CTLSAT
# used for goals
def ast2ltl(ast):
	if len(ast) == 1 and ast[0] == "true":
		return "T"
	elif len(ast) == 1 and ast[0] == "false":
		return "(~T)"
	elif len(ast) == 1:
		return var2chr(int(ast[0][1:]))
	elif ast[0] == "!":
		return "(~"+ast2ltl(ast[1])+")"
	elif ast[0] == "or":
		return "("+ast2ltl(ast[1])+"|"+ast2ltl(ast[2])+")"
	elif ast[0] == "and":
		return "("+ast2ltl(ast[1])+"&"+ast2ltl(ast[2])+")"
	elif ast[0] == "AX":
		return "(X"+	(ast[1])+")"
	elif ast[0] == "AF":
		return "(F"+ast2ltl(ast[1])+")"
	elif ast[0] == "AG":
		return "(G"+ast2ltl(ast[1])+")"
	elif ast[0] == "AU":
		return "("+ast2ltl(ast[1])+"U"+ast2ltl(ast[2])+")"
	elif ast[0] in ["EX", "EG", "EF", "EU"]:
		raise Exception('quantifier E not in LTL \inter CTL fragment')



### translation from RMG arena to CTL theory

# predicate for: "a' := b"
def ASSIGN(a, b):
	if b == "T":
		return "(X"+a+")"
	elif b == "(~T)":
		return "(X~"+a+")"
	else:
		return "("+b+"->(X"+a+"))&(~"+b+"->(X~"+a+"))"

# predicate for: "the variables in vs remain unchanged at the next round"
def UNCH(vs):
	return AND([ASSIGN(var2chr(v), var2chr(v)) for v in vs])

# predicate for: "init command g is executed by a module controlling variables mctrl"
def INITcmd(mctrl, g):
	xs = list()

	if [1 for a in g.actions if a.b.eval([])]: # "x' := T"
		xs.append(AND([var2chr(a.var) for a in g.actions if a.b.eval([])]))

	if [1 for a in g.actions if not a.b.eval([])]: # "x' := F"
		xs.append(AND(["~"+var2chr(a.var) for a in g.actions if not a.b.eval([])]))

	if [1 for v in mctrl if v not in g.ctrl]: # variables not mentioned in g
		xs.append(AND(["~"+var2chr(v) for v in mctrl if v not in g.ctrl]))

	if g.id == -1:
		return AND(xs)
	else:
		return "("+gc2ctl(g.id)+"->("+AND(xs)+"))"

# predicate for: "module m executes exactly one init command"
def INIT(m):
	if m.initexc:
		return X_ONE([INITcmd(m.ctrl, g) for g in m.init])
	else:
		return X_ONE([gc2ctl(g.id) for g in m.init])+"&"+AND([INITcmd(m.ctrl, g) for g in m.init])

# predicate for: "update command g is executed by a module controlling variables mctrl"
def UPDATEcmd(mctrl, g):
	xs = list()

	if g.guard.type != "T": # no need for the guard if T
		xs.append(pl2ctl(g.guard))

	if [1 for a in g.actions]: # "x' := b"
		xs.append(AND([ASSIGN(var2chr(a.var), pl2ctl(a.b)) for a in g.actions]))

	if [1 for v in mctrl if v not in g.ctrl]: # variables not mentioned in g
		xs.append(UNCH([v for v in mctrl if v not in g.ctrl]))

	if g.id == -1:
		return AND(xs)
	else:
		return "("+gc2ctl(g.id)+"->("+AND(xs)+"))"

# predicate for: "module m executes exactly one update command"
def UPDATE(m):
	if valid(plOR([g.guard for g in m.update])):
		# no need for the null-guarded command if there is always an enabled command
		if m.updateexc:
			return X_ONE([UPDATEcmd(m.ctrl, g) for g in m.update])
		else:
			return X_ONE([gc2ctl(g.id) for g in m.update])+"&"+AND([UPDATEcmd(m.ctrl, g) for g in m.update])
	else:
		print "nullCommand"
		nullCommand = "("+UNCH(m.ctrl)+"&"+AND(["~"+pl2ctl(g.guard) for g in m.update])+")"
		return (nullCommand+"|("+X_ONE([UPDATEcmd(m.ctrl, g) for g in m.update])+")")

# CTL theory for a list of modules
def Th(modules):
	i = 0 # we need a unique identifier for each init guarded command
	for m in modules:
		if checkexc(m.init):
			m.initexc = True
			for g in m.init:
				g.id = -1
		else:
			m.initexc = False
			for g in m.init:
				g.id = i
				i += 1
	j = 0 # same for update commands
	for m in modules:
		if checkexc(m.update):
			m.updateexc = True
			for g in m.update:
				g.id = -1
		else:
			m.updateexc = False
			for g in m.update:
				g.id = j
				j += 1

	global Ngc; Ngc = i if i > j else j # number of extra variables needed

	# predicate for: "every module executes exactly one init command"
	INITS = AND([INIT(m) for m in modules])

	# predicate for: "every module executes exactly one update command"
	UPDATES = AND([UPDATE(m) for m in modules])

	return INITS+"&G("+UPDATES+")"



### subroutine for calling CTLSAT

# calls CTLSAT as a subprocess and returns True iff the formula is satisfiable
def SAT(f, v=False):
	raise Exception("Not implemented.")
