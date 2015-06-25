# -*- coding: utf-8 -*-

import unittest
import doctest
import sys
import os
from ctl import *
from checker import *
from networkx import *

class CTLTester(unittest.TestCase):
    def __init__(self, *args):
        super(CTLTester, self).__init__(*args)
        self.knownAtomic = {'f': ['f'],
                  'f1': ['f1'],
                  'f.1': ['f.1'],
                  'pouet': ['pouet'],
                  'true': ['true'],
                  'false': ['false']}
        self.unary = ['!', 'AX', 'AG', 'AF', 'EX', 'EG', 'EF']
        self.binary = ['or', 'and', 'AU', 'EU']
        self.unaryPast = [('<-'+i) for i in ['AX', 'AG', 'AF', 'EX', 'EG', 'EF']]
        self.unaryPast.append('!')
        self.binaryPast = [('<-'+i) for i in ['AU', 'EU']]
        self.binaryPast.append('or')
        self.binaryPast.append('and')
        self.simplified = {'!true': 'false',
                           '!false': 'true',
                           'or true p': 'true',
                           'or false p': 'p',
                           'and true p': 'p',
                           'and false p': 'false',
                           '!!p': 'p'}

    def testAtomic(self):
        ''' Test for the syntax of CTL atomic predicates '''
        for i in self.knownAtomic.keys():
            self.assertEquals(CTL(i).ast, self.knownAtomic[i])

    def testAtomicPast(self):
        ''' Test for the syntax of CTL atomic predicates with reverse operators'''
        for i in self.knownAtomic.keys():
            self.assertEquals(CTL(i).ast, self.knownAtomic[i])

    def testUnary(self):
        ''' Test for the syntax of CTL unary operators '''
        for op in self.unary:
            for f in self.knownAtomic.keys():
                self.assertEquals(CTL(op+' '+f).ast, [op, [f]])

    def testUnaryPast(self):
        ''' Test for the syntax of CTL unary operators with reverse operators'''
        for op in self.unaryPast:
            for f in self.knownAtomic.keys():
                self.assertEquals(CTL(op+' '+f).ast, [op, [f]])

    def testBinary(self):
        ''' Test for the syntax of CTL binary operators '''
        for op in self.binary:
            for f in self.knownAtomic.keys():
                for g in self.knownAtomic.keys():
                    self.assertEquals(CTL(op+' '+f+' '+g).ast, [op, [f], [g]])

    def testBinaryPast(self):
        ''' Test for the syntax of CTL binary operators with reverse operators'''
        for op in self.binaryPast:
            for f in self.knownAtomic.keys():
                for g in self.knownAtomic.keys():
                    self.assertEquals(CTL(op+' '+f+' '+g).ast, [op, [f], [g]])

    def testSimplify(self):
        ''' Test for the simplification of CTL formulas '''
        for p in self.knownAtomic.keys():
            self.assertEquals(CTL(p).simplify(), CTL(p))

        for p in self.simplified.keys():
            self.assertEquals(CTL(p).simplify(), CTL(self.simplified[p]))


if __name__ == '__main__':
    if not '-v' in sys.argv:
        print 'Use python test.py -v for verbose output'

    suite = unittest.TestSuite()
    suite.addTest(doctest.DocFileSuite(os.path.join('tests', 'canonic_test.txt')))
    suite.addTest(doctest.DocFileSuite(os.path.join('tests', 'freevars_test.txt')))
    suite.addTest(doctest.DocFileSuite(os.path.join('tests', 'matching_test.txt')))  
    suite.addTest(doctest.DocFileSuite(os.path.join('tests', 'substitutions_test.txt')))                 
    suite.addTest(doctest.DocFileSuite(os.path.join('tests', 'dataflow_test.txt')))
    suite.addTest(doctest.DocFileSuite(os.path.join('tests', 'checker_test.txt')))
    suite.addTest(doctest.DocFileSuite(os.path.join('tests', 'microwave_test.txt')))
    suite.addTest(doctest.DocFileSuite(os.path.join('tests', 'examples_unittest.txt')))
    unittest.TextTestRunner(verbosity=2).run(suite)

    unittest.main()
