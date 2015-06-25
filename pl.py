# This module defines a class for Propositional Logic (PL) formulae
# The set of propositional letters is written x0, x1, ... and variables are stored as ints.
# A valuation is simply a list of ints: variable x_n evaluates to True iff n is in the list
# A PL instance has a method eval which, given a valuation list, returns True iff the valuation satisfies the formula

from mrwaffles.ctl import *

class PL:
	def __repr__(self):
		return repr(self)

class T(PL):
	def __init__(self):
		self.type = "T"

	def __repr__(self):
		return "T"

	def eval(self, v):
		return True

	def FV(self):
		return []

T = T()

class F(PL):
	def __init__(self):
		self.type = "F"

	def __repr__(self):
		return "F"

	def eval(self, v):
		return False

	def FV(self):
		return []

F = F()

class Var(PL):
	def __init__(self, n):
		self.n = n
		self.type = "Var"

	def __repr__(self):
		return "x"+str(self.n)

	def eval(self, v):
		return self.n in v
	
	def FV(self):
		return [self.n]

class Not(PL):
	def __init__(self, p):
		self.p = p
		self.type = "Not"

	def __repr__(self):
		return "!"+repr(self.p)
	
	def eval(self, v):
		return not self.p.eval(v)

	def FV(self):
		return self.p.FV()

class Or(PL):
	def __init__(self, p, q):
		self.p = p
		self.q = q
		self.type = "Or"

	def __repr__(self):
		return "(or "+repr(self.p)+" "+repr(self.q)+")"

	def eval(self, v):
		return self.p.eval(v) or self.q.eval(v)

	def FV(self):
		return self.p.FV()+self.q.FV()

class And(PL):
	def __init__(self, p, q):
		self.p = p
		self.q = q
		self.type = "And"

	def __repr__(self):
		return "(and "+repr(self.p)+" "+repr(self.q)+")"

	def eval(self, v):
		return self.p.eval(v) and self.q.eval(v)

	def FV(self):
		return self.p.FV()+self.q.FV()


# translates the abstract syntax tree of a formula into a PL instance
def ast2pl(ast):
	if len(ast) == 1 and ast[0] == "F":
		return F
	elif len(ast) == 1 and ast[0] == "T":
		return T
	elif len(ast) == 1: 
		assert(ast[0][0] == 'x')
		return Var(int(ast[0][1:]))
	elif ast[0] == "!":
		return Not(ast2pl(ast[1]))
	elif ast[0] == "or":
		return Or(ast2pl(ast[1]), ast2pl(ast[2]))
	elif ast[0] == "and":
		return And(ast2pl(ast[1]), ast2pl(ast[2]))

# parses a propositional formula in MrWaffles syntax
def parsePL(s):
	ast = CTL.parse(s)
	return ast2pl(ast)

# returns a[b/xn]
def sub(a, n, b):
	if a.type == "Var" and a.n == n:
		return b

	elif a.type in ["Var", "T", "F"]:
		return a

	elif a.type == "Not":
		return Not(sub(a.p, n, b))

	elif a.type == "Or":
		return Or(sub(a.p, n, b), sub(a.q, n, b))

	elif a.type == "And":
		return And(sub(a.p, n, b), sub(a.q, n, b))

def simplify(f):
	if f.type == "Not":
		if f.p.type == "T":
			return F

		elif f.p.type == "F":
			return T
	
		return Not(simplify(f.p))

	elif f.type == "Or":
		if f.p.type == "T" or f.q.type == "T":
			return T
		
		elif f.p.type == "F" and f.q.type == "F":
			return F

		return Or(simplify(f.p), simplify(f.q))


	elif f.type == "AND":
		if f.p.type == "T" and f.q.type == "T":
			return T
		
		elif f.p.type == "F" or f.q.type == "F":
			return F

		return And(simplify(f.p), simplify(f.q))

	else:
		return f

def plOR(fs):
	if len(fs) == 0:
		return T
	elif len(fs) == 1:
		return fs[0]
	else:
		n = len(fs)
		return Or(plOR(fs[:n/2]), plOR(fs[n/2:]))

def sat(f):
	if f.type == "T":
		return True
	
	elif f.type == "F":
		return False

	elif not f.FV():
		return f.eval([])

	elif sat(simplify(sub(f, f.FV()[0], T))):
		return True
	
	else:
		return sat(simplify(sub(f, f.FV()[0], F)))

def valid(f):
	return not sat(Not(f))
