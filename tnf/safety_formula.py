import copy
import itertools
from os import pipe

from parsimonious.grammar import Grammar
from parsimonious.nodes import NodeVisitor
from z3 import *

from temporal_formula import TemporalFormula


import copy
import utils



class SafetyFormula(NodeVisitor):
    """
    Safety Formula is conjuntion of n implications (Safety Formula Children), each implication is called child
    We represent de Safety formula as a n-ary tree
    """

    def __init__ (self, formulasStr):
        self.formulasStr = formulasStr
        self.ab = ['&']
        self.__parse_children()

   
    def __parse_children(self):
        for formulaStr in self.formulasStr:
            formula = TemporalFormula(formulaStr)
            self.ab.append(formula.ab)



        
