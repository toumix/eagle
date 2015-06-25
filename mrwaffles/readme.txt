    Mr. Waffles

Author: Daniel Reynaud <reynaud.daniel@gmail.com>
Blog: http://indefinitestudies.org
Developed at Nancy University - Loria - France


Mr. Waffles is an open source CTL model checker, based on the classic algorithm
by Clarke et al. Written entirely in Python, it allows for quick prototyping of
systems and specifications. It supports an extension of CTL with reverse 
operators, free variables and quantification over finite paths.

It is particularly suited for the analysis of control-flow graphs, to prove 
data-flow and behavioral properties.


I. Installation
** *** ***** *******
There is no installer for this program. It is 100% pure Python, so it should
run on any system with a suitable Python interpreter installed. We do not
provide an installer to the site-packages either.


II. Requirements
** *** ***** *******
- Operating system: any

- Python 2.6.2

- networkx: a Python module for graph manipulation (works with version 1.0.dev)
See http://networkx.lanl.gov/ for installation instructions.

- pyparsing: a Python module for CTL parsing (works with version 1.5.2). See 
http://pyparsing.wikispaces.com/ for installation instructions.

- (optional) pydot: a Python module for graph rendering (works with version 
0.9.10). See http://dkbza.org/pydot.html for installation instructions.


III. Quick Launch
** *** ***** *******
You can check that your version of Mr. Waffles is working correctly by running
$ python test.py -v

Then, the simplest way to try Mr. Waffles is to run python -i checker.py from 
your favorite shell. Try something like:
$ python -i checker.py
>>> g = PredicatedGraph()
>>> g.add_edge(1, 2)
>>> g.add_predicate(1, 'first')
>>> g.add_predicate(2, 'next')
>>> g.check('EX next')
set([1])

See examples/examples.txt for more use cases and examples of CTL syntax,
checking with free variables and other interesting features.
