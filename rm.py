# This module defines the concrete data structures for Reactive Module Games.
# It implements utility functions, and the parsing of input files.

from mrwaffles.ctl import *
from pl import *

from collections import namedtuple
from itertools import product

# defines an action "var := b"
class Action(namedtuple('Action', ['var', 'b'])):
	def __repr__(self):
		return "x"+repr(self.var)+"' := "+repr(self.b)

# defines a command "guard -> var1 := b1, var2 := b2, ..."
class Command(namedtuple('Command', ['guard', 'actions'])):
	def __repr__(self):
		return repr(self.guard)+" -> "+repr(self.actions)

	def __init__(self, guard, actions):
		self.ctrl = [a.var for a in self.actions]

# defines a module "m = (Phi, I, U)"
class RM(namedtuple('RM', ['ctrl', 'init', 'update'])):
	def __repr__(self):
		s = "m controls "+str(self.ctrl)
		s += "\ninit"
		for g in self.init:
			s += "\n\t"+str(g)
		s += "\nupdate"
		for g in self.update:
			s += "\n\t"+str(g)

# returns the valuation obtained from the execution of command g on valuation v in module m 
def exe(m, g, v):
	unch = [n for n in set(v).intersection(m.ctrl).difference(g.ctrl)] # the variables g leaves unchanged
	updt = [a.var for a in g.actions if a.b.eval(v)] # the variables g actually updates
	return sorted(updt+unch)

# returns the valuation obtained by executing a joint guarded command
def jointExe(modules, J, v):
	N = len(modules)
	w = []
	for i in range(N):
		w += exe(modules[i], J[i], v)
	return sorted(w)

# returns the list of commands enabled for module m at valutation v
def enabled(m, v):
	if [(m, g) for g in m.update if g.guard.eval(v)]:
		return [g for g in m.update if g.guard.eval(v)]
	else:
		return [Command(T, [])]

# returns the list of commands enabled for module m at initiation
def enabled_init(m):
	if [(m, g) for g in m.init if g.guard.eval([])]:
		return [g for g in m.init if g.guard.eval([])]
	else:
		return [Command(T, [])]

# returns the cartesian product of enabled commands for a list of modules, at valuation v
def jointEnabled(modules, v):
	return product(*[enabled(m, v) for m in modules])

# returns the cartesian product of enabled commands for a list of modules, at initiation
def jointEnabled_init(modules):
	return product(*[enabled_init(m) for m in modules])


# These functions parse the input file into RM instances.

# parses a list of actions
def parseActions(xs):
	l = list()
	for x in xs.split(', '):
		assert(len(x.split("' := ")) == 2)
		var = int(x.split("' := ")[0][1:])
		b = parsePL(x.split("' := ")[1])
		l.append(Action(var, b))
	return l

# parses a guarded command
def parseCommand(g):
	assert(len(g.split(' -> ')) == 2)

	guard = parsePL(g.split(' -> ')[0])
	actions = parseActions(g.split(' -> ')[1])

	return Command(guard, actions)

# parses a reactive module
def parseRM(m):
	return RM(m['ctrl'], [parseCommand(g) for g in m['init']], 
		[parseCommand(g) for g in m['update']])

# returns True iff the semantics of g1 and g2 exclude one another
def mutexc(g1, g2):
	if not sat(And(g1.guard, g2.guard)):
		return True
	else:
		for a in g1.actions:
			for b in g2.actions:
				if b.var == a.var:
					if not sat(And(And(g1.guard, g2.guard), And(Not(a.b), Not(b.b)))):
						if not sat(And(And(g1.guard, g2.guard), And(a.b, b.b))):
							return True
		return False

def checkexc(gs):
	for g1 in gs:
		for g2 in gs:
			if g1 != g2 and not mutexc(g1, g2):
				return False
	return True
