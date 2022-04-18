from parsimonious.grammar import Grammar
from parsimonious.nodes import NodeVisitor
import sys
from utils import utils

class TemporalFormula(NodeVisitor):

    """
        Temporal Formula is a formula in XNNF, that is, it follows the NNF but also include Evetually(limited) and next unary temporal operators.
        We represent the temporal fomula as a binary tree
    """

    def __init__ (self, str, changeNegAlwaysEventually = True):
        sys.setrecursionlimit(100000)
        self.changeNegAlwaysEventually = changeNegAlwaysEventually
        self.devStr = str.replace("\t","").replace(" ", "").replace("\n","")
        self.ast = self.__parse_formula(self.devStr) #Formula as an ast tree
        self.nnf = self.__push_negs(self.visit(self.ast)) #Push negs
        self.ab = self.__push_nexts(self.nnf) #Push Nexts
        self.now_e = self.__now_e(self.ab) #Get now_e
        self.str = utils.to_str(self.ab)

    def generic_visit(self, node, children):    

        if len(children) == 0:
            return node.text
        elif len(children) == 1:
            return children[0]
        elif len(children) == 2:
            if utils.is_neg(children[0]):
                return ["-", children[1]]
            else: #Eventually and Globally
                return [children[0], children[1]]
        elif children[0] == "(":
            return children[1]
        else:
            if children[1] == "->":
                return ["|", ["-", children[0]], children[2]]
            elif children[1] == "<-->":
                return ['&', ["|",["-", children[0]],children[2]], ["|",["-", children[2]],children[0]]]
            elif children[1] == '==' or children[1] == '=':
                return children[2]
            else:
                if utils.is_and(children[1]):
                    return ["&", children[0], children[2]]
                else:
                    return ["|", children[0], children[2]]



    
    def __now_e(self, formula):
        if isinstance(formula, str):
            if  utils.is_var_env(formula):
                return {formula}
            else:
                return set()
        elif len(formula) == 2:
            if utils.is_neg(formula[0]):
                return self.__now_e(formula[1])
            elif utils.is_next(formula[0]):
                return set()
            else:
                if utils.is_always(formula[0]) or utils.is_eventually(formula[0]):
                    limitInf, _ =  utils.get_temporal_op_limits(formula[0])
                    if int(limitInf) == 0:
                        return self.__now_e(formula[1])    
                return set()
        else:
            now_leftFormula = self.__now_e(formula[1])
            now_rightFormula = self.__now_e(formula[2])
            return now_leftFormula | now_rightFormula
    
    def neg(self, formula):
        if isinstance(formula, str) and utils.is_true(formula):
            return "False"
        elif isinstance(formula, str) and utils.is_false(formula):
            return "True"
        elif utils.is_neg(formula[0]):
            return formula[1]
        elif utils.is_and(formula[0]):
            leftFormulaNeg = self.neg(formula[1])
            rightFormulaNeg = self.neg(formula[2])
            return ["|",leftFormulaNeg, rightFormulaNeg]
        elif utils.is_or(formula[0]):
            leftFormulaNeg = self.neg(formula[1])
            rightFormulaNeg = self.neg(formula[2])
            return ["&",leftFormulaNeg, rightFormulaNeg]
        elif utils.is_next(formula[0]):
            subformulaNeg = self.neg(formula[1])
            return ['X', subformulaNeg]
        elif utils.is_eventually(formula[0]):
            subformulaNeg = self.neg(formula[1])
            if self.changeNegAlwaysEventually:
                return [utils.F_to_G(formula[0]), subformulaNeg]
            else:
                return ["-", formula]

        elif utils.is_always(formula[0]):
            subformulaNeg = self.neg(formula[1])
            if self.changeNegAlwaysEventually:
                return [utils.G_to_F(formula[0]), subformulaNeg]
            else:
                return ["-", formula]

        else:
            return ["-", formula]



    def next (self, formula, c):
        if utils.is_and(formula[0]):
            leftFormulaNext = self.next(formula[1], c)
            rightFormulaNext = self.next(formula[2], c)
            return ["&",leftFormulaNext, rightFormulaNext]

        elif utils.is_or(formula[0]):
            leftFormulaNext = self.next(formula[1], c)
            rightFormulaNext = self.next(formula[2], c)
            return ["|",leftFormulaNext, rightFormulaNext]

        elif utils.is_next(formula[0]):
            c +=1
            subformulaNext = self.next(formula[1], c)
            return subformulaNext
        elif utils.is_eventually(formula[0]):
            limitInf, limitSup =  utils.get_temporal_op_limits(formula[0])
            subformulaXnnf = self.__push_nexts(formula[1])
            newOp = "F[" + str(int(limitInf)+c) + "," + str(int(limitSup)+c) + "]"
            return [newOp, subformulaXnnf]
        elif utils.is_always(formula[0]):
            limitInf, limitSup =  utils.get_temporal_op_limits(formula[0])
            subformulaXnnf = self.__push_nexts(formula[1])
            newOp = "G[" + str(int(limitInf)+c) + "," + str(int(limitSup)+c) + "]"
            return [newOp, subformulaXnnf]

        else:
            return self.generar_next(formula, c)

    def generar_next(self, formula, n):
        if n == 1:
            return ['X', formula]
        else:
            return ['X', self.generar_next(formula, n-1)]

    def __push_negs(self, formula):
        if utils.is_neg(formula[0]):
            if isinstance(formula[1], str) or (not self.changeNegAlwaysEventually and  utils.is_eventually(formula[1][0])) or (not self.changeNegAlwaysEventually and  utils.is_always(formula[1][0])):
                return formula
            formulaNeg = self.neg(formula[1])
            return self.__push_negs(formulaNeg)
        elif utils.is_unary(formula):
            rightFormulaNeg = self.__push_negs(formula[1])
            return [formula[0], rightFormulaNeg]
        elif utils.is_binary(formula):
            leftFormulaNeg = self.__push_negs(formula[1])
            rightFormulaNeg = self.__push_negs(formula[2])
            return [formula[0],leftFormulaNeg, rightFormulaNeg]
            
        else:
            return formula
    
    def __push_nexts(self, formula):
        if utils.is_neg(formula[0]):
            rightFormulaNext = self.__push_nexts(formula[1])
            return ['-', rightFormulaNext]
        elif utils.is_and(formula[0]):
            leftFormulaNext = self.__push_nexts(formula[1])
            rightFormulaNext = self.__push_nexts(formula[2])
            return ["&",leftFormulaNext, rightFormulaNext]

        elif utils.is_or(formula[0]):
            leftFormulaNext = self.__push_nexts(formula[1])
            rightFormulaNext = self.__push_nexts(formula[2])
            return ["|",leftFormulaNext, rightFormulaNext]

        elif utils.is_next(formula[0]):
            rightFormulaNext = self.next(formula[1], 1)
            return rightFormulaNext
            
        else:
            return formula


    def __parse_formula(self, str):
            grammar = Grammar(
                """
                Bicondicional = (Condicional "<-->" Bicondicional) / Condicional
                Condicional = (Disyuncion "->" Condicional) / Disyuncion
                Disyuncion =  (Conjuncion ("||" / "|")  Disyuncion) / Conjuncion
                Conjuncion = (Literal ("&&"/"&") Conjuncion) / Literal
                Literal =  (Atomo) / ((Neg / Eventually / Next / Globally ) Literal)
                Atomo =  Var / Enum / Agrupacion
                Enum = (Var ("==" / "=") Var) / Var
                Agrupacion = ("(" Bicondicional ")") 
                Var = ~"[a-zA-EH-WY-Z0-9][a-zA-Z0-9_]*"
                Next = "X"
                Eventually = ~"F\[[0-9]+\,[0-9]+\]" 
                Globally = ~"G\[[0-9]+\,[0-9]+\]"
                Neg = "!" / "-" / "~"
                """

            )
            """ try: 
                parse_formula = grammar.parse(str)
            except Exception as e:
                print(e)
                print("Fail parsing xnnf formula")
                print(str)
                parse_formula = None
                exit(0)
 """
            parse_formula = grammar.parse(str)
            return parse_formula

