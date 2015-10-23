#export PYTHONPATH=/auto/users/ug12at2/Documents/project/networkx

# This is the main module of the project.
# It implements the command line interface for calling the algorithm.

import time, sys, argparse, pickle

from rm import *
from arena2kripke import *
import thctl
import thltl

# the main algorithm
def Membership(modules, goals, strategies, verbose, ctlmode):
	assert(len(modules)==len(goals))
	assert(len(goals)==len(strategies))

	N = len(modules)

	start = time.time()*1000
	if verbose:
		print "Building the outcome ..."

	(A, S0) = Arena2Kripke(strategies)

	perfA2K = time.time()*1000 - start
	if verbose:
		print str(A.number_of_nodes())+" nodes and "+str(A.number_of_edges())+" edges. ("+str(round(perfA2K))+" ms)"
		print

	# time counters for model checking and SAT solving
	perfMC = 0.0
	perfSAT = 0.0

	for i in range(N):
		start = time.time()*1000 # timestamp for measuring model checking performances

		if not entails(A, S0, goals[i]):

			perfMC += time.time()*1000 - start

			print "Player "+str(i)+" does not get its goal satisfied."
			if verbose:
				print
				print "SAT solving ..."

			start = time.time()*1000 # timestamp for measuring SAT solving performances

			if ctlmode:
				theory = thctl.Th([modules[i]]+strategies[:i]+strategies[i+1:])
				goal = thctl.ast2ctl(CTL.parse(goals[i]))

				if thctl.SAT(goal+'^'+theory, verbose):
					print "(Size of the CTL theory: "+str(len(theory))+")"
					perfSAT += time.time()*1000 - start

					print
					print "It could change its strategy to get its goal satisfied:"
					print
					print "\tNot a Nash Equilibrium."

					if verbose:
						print
						print "Model checking: \t"+str(round(perfMC))+" ms"
						print "CTL SAT solving: \t"+str(round(perfSAT))+"ms"

					return False
				else:
					perfSAT += time.time()*1000 - start
					print
					print "But it cannot change its strategy to satisfy it."
			else:
				theory = thltl.Th([modules[i]]+strategies[:i]+strategies[i+1:])
				goal = thltl.ast2ltl(CTL.parse(goals[i]))
				print goal+'&'+theory
				return True

		else:
			perfMC += time.time()*1000 - start
			print "Player "+str(i)+" gets its goal achieved."

	print
	print "\tThis is a Nash Equilibrium."

	if verbose:
		print
		print "Model checking: \t"+str(round(perfMC))+" ms"
		print "CTL SAT solving: \t"+str(round(perfSAT))+" ms"

	return True


def main(argv=None):
# parses the command line arguments and calls Membership
	argparser = argparse.ArgumentParser(description='CTL RMG Equilibrium Checker')
	argparser.add_argument('inputf')
	argparser.add_argument('-c', '--ctlmode', action="store_false", default=True)
	argparser.add_argument('-v', '--verbose', action="store_true", default=False)
	args = argparser.parse_args(sys.argv[1:])

	f = open(args.inputf)
	d = eval(f.read())

	modules = [parseRM(m) for m in d['modules']]
	strategies = [parseRM(m) for m in d['strategies']]

	Membership(modules, d['goals'], strategies, args.verbose, args.ctlmode)

if __name__ == '__main__':
    main()
