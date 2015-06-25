# -*- coding: utf-8 -*-
import_ok = 1
from ctl import *
import functools
import cPickle
try:
    from networkx import Graph, DiGraph, strongly_connected_component_subgraphs, draw
except:
    import_ok = 0

__version__ = 9.07

class PredicatedGraph(DiGraph):
    def __init__(self, name=''):
        DiGraph.__init__(self)
        self.predicates = {}
        self.reversed = None
        self.atoms = set([])

    def refresh_reversed(self):
        self.reversed = self.reverse()

    def get_reversed(self):
        if self.reversed is None:
            self.refresh_reversed()
        return self.reversed
        
    def add_predicate(self, n, p):
        ''' adds predicate p to node n\n
        p can be a CTL instance or a string '''
        newp = p
        if isinstance(p, str):
            newp = CTL(p)
        if not n in self:
            self.add_node(n)
        try:
            self.predicates[n].append(newp)
        except:    # n has no predicate yet
            self.predicates[n] = [newp]
        self.atoms |= newp.atoms()
  
    def has_predicate(self, n, p):
        ''' returns True iff node n has a predicate that matches p\n
        p can be a CTL instance or a string '''
        try:
            for term in self.predicates[n]:
                if term << p:
                    return True
            return False
        except KeyError: # node n has no predicate yet
            return False
    
    def nontrivial_strongly_connected_components(self):
        ''' iterator over nontrivial strongly connected subgraphs\n
        nontrivial means it has more than one node or it is a node with a self loop '''
        scc = strongly_connected_component_subgraphs(self)
        for g in scc:
            if g.number_of_nodes()>1 or g.number_of_selfloops()>0:
                yield g

    def terminals(self):
        ''' returns a list of nodes with no successors '''
        result = set([])
        for n in self.nodes():
            if len(self.successors(n)) == 0:
                result |= set([n])
        return result

    def transitive_predecessors(self, node):
        ''' returns a list of nodes n such that there is a path from n to node '''
        result, done = set([]), set([])
        todo = set(self.predecessors(node))
        while todo:
            n = todo.pop()
            if not n in done:
                result |= set([n])
                todo |= set(self.predecessors(n))
            done |= set([n])
        return result

    # taken from http://pko.ch/2008/08/22/memoization-in-python-easier-than-what-it-should-be/
    def memoize(fctn):
        memory = {}
        @functools.wraps(fctn)
        def memo(*args,**kwargs):
            haxh = cPickle.dumps((args, sorted(kwargs.iteritems())))

            if haxh not in memory:
                memory[haxh] = fctn(*args,**kwargs)

            return memory[haxh]
        if memo.__doc__:
            memo.__doc__ = "\n".join([memo.__doc__,"This function is memoized."])
        return memo

    # disabled for the moment, too unstable
    #@memoize
    def check(self, formula, canonic=False, debug=False):
        ''' returns the list of nodes in this graph that satisfy formula\n
        formula can be a CTL instance or a string '''
        newf = formula
        if isinstance(formula, str):
            newf = CTL(formula)
        return set([i for i in self.check_iter(newf, canonic, debug)])

    #@memoize
    def check_iter(self, formula, canonic=False, debug=False):
        ''' iterator over nodes in this graph that satisfy the formula\n
        formula can be a CTL instance or a string '''
        if formula.is_reverse():
            # we are checking a reverse formula, we must work on the reverse graph
            graph = self.get_reversed()
        else:
            graph = self

        if formula << 'true':
            for i in graph.nodes():
                yield i

        elif formula << 'false':
            return

        elif formula.is_term():
            for i in graph.nodes():
                if self.has_predicate(i, formula):
                    yield i
        
        elif formula.op == Not:
            op, f = ~formula
            subcheck = self.check(f, canonic, debug)
            if debug:
                print 'check(%s) = %s' % (f, subcheck)

            for i in set(graph.nodes()) - set(subcheck):
                yield i

        elif formula.op == Or or formula.op == And:
            op, f, g = ~formula
            subcheckf = self.check(f, canonic, debug)
            subcheckg = self.check(g, canonic, debug)
            if debug:
                print 'check(%s) = %s' % (f, subcheckf)
                print 'check(%s) = %s' % (g, subcheckg)

            if formula.op == Or:
                for i in (set(subcheckf)
                        | set(subcheckg)):
                    yield i
            else: # And
                for i in (set(subcheckf)
                        & set(subcheckg)):
                    yield i

        elif formula.op == EX or formula.op == RevEX:
            op, f = ~formula
            subcheck = self.check(f, canonic, debug)
            if debug:
                print 'check(%s) = %s' % (f, subcheck)

            for i in graph.nodes():
                succ = set(graph.successors(i))
                # if one of the successors of i satisfies f
                if (succ & set(subcheck)):
                    yield i

        elif formula.op == EU or formula.op == RevEU:
            op, f, g = ~formula
            subcheckf = self.check(f, canonic, debug)
            subcheckg = self.check(g, canonic, debug)
            if debug:
                print 'check(%s) = %s' % (f, subcheckf)
                print 'check(%s) = %s' % (g, subcheckg)

            T = set(subcheckg)
            done = set([])
            for i in T:
                done |= set([i])
                yield i

            while T:
                s = T.pop()
                for t in graph.predecessors(s):
                    if not t in done and t in subcheckf:
                        done |= set([t])
                        T |= set([t])
                        yield t

        # only infinite paths will be considered by EGi
        elif formula.op == EGi or formula.op == RevEGi:
            op, f = ~formula
            subcheck = self.check(f, canonic, debug)
            if debug:
                print 'check(%s) = %s' % (f, subcheck)

            S2 = set(subcheck)
            done = set([])

            # A directed graph is strongly connected if there is a path
            # from each vertex in the graph to every other vertex.
            # T is the set of nodes in a strongly connected component of graph
            T = set([])
            for c in graph.subgraph(S2).nontrivial_strongly_connected_components():
                T |= set(c.nodes())

            if debug:
                print 'checking EG formula, the set of nodes in a SCC is %s' % T

            for s in T:
                done |= set([s])
                yield s
        
            while T:
                s = T.pop()
                for t in S2 & set(graph.predecessors(s)):
                    if not t in done:
                        done |= set([t])
                        T |= set([t])
                        yield t

        # the EG operator will only look for finite paths
        elif formula.op == EG or formula.op == RevEG:
            op, f = ~formula
            subcheck = self.check(f, canonic, debug)
            if debug:
                print 'check(%s) = %s' % (f, subcheck)

            path_to_terminals = set([])
            for n in self.terminals() & subcheck: # only terminals that satisfy f
                path_to_terminals |= set([n]) | self.subgraph(subcheck).transitive_predecessors(n)

            for n in set(subcheck) & path_to_terminals:
                yield n

        else:
            if debug:
                print 'Trying to use canonic form of ' + formula
            if canonic:
                raise (NotImplementedError, 
                    'Can not check this type of formula for the moment: '+formula)
            else:
                for i in self.check_iter(formula.canonic().simplify(), True, debug):
                    yield i

    def check_with_freevars(self, formula, canonic=False, debug=False):
        ''' returns the set of nodes in this graph that satisfy the formula\n
            formula can be a CTL instance or a string\n
            free variables in formula will be substituted with atoms '''
        newf = formula
        if isinstance(formula, str):
            newf = CTL(formula)
        return set([i for i in self.check_with_freevars_iter(newf, canonic, debug)])

    # might yield multiple times the same node
    def check_with_freevars_iter(self, formula, canonic=False, debug=False):
        for sub in self.get_substitutions(formula):
            if debug:
                print 'Using substitution %s' % sub
            substituted = formula.substitute(sub)
            for n in self.check_iter(substituted, canonic, debug):
                yield n

    # this *really* is a dirty hack -_-'
    def get_substitutions(self, formula):
        fv = formula.freevars()
        for sub in self.arrange(fv, self.atoms):
            yield sub

    # there is no reason for this method to be in this class
    def arrange(self, fv, avail):
        if len(fv) >= 1:
            head = fv.pop()
            for i in avail:
                newavail = avail - set([i])
                for sub in self.arrange(list(fv), newavail):
                    sub[head] = i
                    yield sub
        else:
            yield {}

    def dot(self, name):
        ''' render this graph in $name.jpg using pydot '''
        try:
            import pydot
        except:
            raise Exception('Error importing pydot, can not plot this graph')

        g = pydot.Dot(name=name)
        g.set_type('digraph')
        
        for node in self.nodes():
            label = str(node)+'\\n'
            predicates = ''
            if self.predicates.has_key(node):
                predicates = ', '.join([str(x) for x in self.predicates[node]])
            g.add_node(pydot.Node(str(node), label=label+predicates))
        for edge in self.edges():
            g.add_edge(pydot.Edge(str(edge[0]), str(edge[1])))
        g.write_jpeg(name+'.jpg') 


def main():
    if not import_ok:
        print('Fatal error: could not find module networkx')
        exit(1)

    print 'Mr. Waffles version %s' % __version__
    print 'I am supposed to run from an interactive python shell.'
    print 'You can also import me as a library.'

if __name__ == '__main__':
    main()
