
from ast import parse
import copy
import itertools
import sys
from traceback import print_tb
from utils import utils
from temporal_formula import TemporalFormula
from run_bica import prime_cover_via_BICA
import warnings
warnings.filterwarnings("ignore", category=RuntimeWarning) 

class TNF:
    def __init__(self, formula):
        self.formula = formula
        self.tnfFormula = self.tnf()
        self.tnfStr = print_formula(self.tnfFormula)

    def __literals(self, separated_formula):
        return separated_formula[0]

    def __future_formulas(self, separated_formula):
        return separated_formula[1]

    def __hold_condition(self, literals_i, literals_j):
        for literal_i in literals_i:
            neg_literal_i = utils.get_neg_literal(literal_i)
            if neg_literal_i in literals_j:
                return True
        return False

    def __get_common_literals(self, literals_i, literals_j):
        return literals_i.intersection(literals_j)

    def __get_different_literals(self, literals_i, literals_j):
        return literals_i-literals_j, literals_j-literals_i

    def __dnf_literals(self, d, di, negdj, future):
        if negdj == set():
            return False
        l = [False, True]
        negdj_assigment = self.__get_assigment(negdj) 
        assigments = set(itertools.product(l, repeat=len(negdj))) - negdj_assigment 
        res = list()
        for assigment in assigments:
            negdj_dnf = set()
            negdj_list = list(negdj)
            for i, is_true in enumerate(assigment):
                var_i = utils.get_variable(negdj_list[i])
                if is_true:
                    negdj_dnf.add(var_i)
                else:
                    neg_literal_i = utils.get_neg_literal(var_i)
                    negdj_dnf.add(neg_literal_i)

            res.append([d.union(di).union(negdj_dnf), future])
        return res

    def __get_assigment(self, f):
        ass = list()
        for l in f:
            if l[0] == "-":
                ass.append(False)
            else:
                ass.append(True)
        return {tuple(ass)}


    def __apply_join_rule(self, literals_i, literals_j, future_formulas_i, future_formulas_j):
        d =  self.__get_common_literals(literals_i, literals_j)
        d1, d2 = self.__get_different_literals(literals_i, literals_j)
        join_futures = self.__join_futures(future_formulas_i, future_formulas_j)
        new_join_1 = [d.union(d1).union(d2), join_futures]
        new_join_2 = self.__dnf_literals(d, d1, d2, future_formulas_i)
        new_join_3 = self.__dnf_literals(d, d2, d1, future_formulas_j)
        return new_join_1, new_join_2, new_join_3
            
    def __join_futures(self, future1, future2):
        join_f = copy.copy(future1)
        for f2 in future2:
            added = False
            for f1 in future1:
                if f1 < f2 and f1 != set():
                    join_f.remove(f1)
                    join_f.append(f2)
                    added = True
                elif f1 == f2:
                    added = True
                else:
                    continue
            if not added:    
                join_f.append(f2)
        return join_f
            




    def tnf(self):
        formula = copy.deepcopy(self.formula)
        all_hold_condition = False
        while not all_hold_condition:
            for index_i, separated_formula_i in enumerate(formula):
                changed = False
                for index_j, separated_formula_j in enumerate(formula):
                    if index_i == index_j:
                        continue
                    
                    literals_i = self.__literals(separated_formula_i)
                    literals_j =  self.__literals(separated_formula_j)
                    if not self.__hold_condition(literals_i, literals_j):
                        #print("\n Formula: ",  print_formula(formula))
                        #print("\n 1- ", separated_formula_i)
                        #print("\n 2- ", separated_formula_j)
                        formula = [v for i, v in enumerate(formula) if i not in {index_i, index_j}]
                        future_formulas_i = self.__future_formulas(separated_formula_i)
                        future_formulas_j =  self.__future_formulas(separated_formula_j)
                        new_sf_1, new_sf_2, new_sf_3 = self.__apply_join_rule(literals_i, literals_j, future_formulas_i, future_formulas_j)

                        formula.append(new_sf_1)
                        if new_sf_2:
                            for new_sf_2_i in new_sf_2:
                                formula.append(new_sf_2_i)
                        if new_sf_3:
                            for new_sf_3_i in new_sf_3:
                                formula.append(new_sf_3_i)
                        changed = True
                        #print("\n No cumple condicion, genera: ",print_formula(formula))
                        break
                    #else:
                        #print("\n Cumple condicion")
                if changed:
                    break
            if not changed:
                all_hold_condition = True
        return formula

def print_formula(formula):
        res = ""
        for fi in formula:
            literal_fi = fi[0]
            futures_fi = fi[1]
            literals_str = ""
            for li_fi in list(literal_fi):
                if literals_str == "":
                    literals_str += li_fi
                else:
                    literals_str += " ∧ " +li_fi
            futures_str = ""
            for futuresi_fi in futures_fi:
                and_futures_ij = ""
                for futuresij_fi in futuresi_fi:
                    if and_futures_ij == "":
                        and_futures_ij += futuresij_fi
                    else:
                        and_futures_ij += " ∧ " +and_futures_ij

                if futures_str == "":
                    futures_str += and_futures_ij
                else:
                    futures_str += " v " + and_futures_ij
            futures_str = "(" + futures_str + ")"
            if res == "":
                res += "(" + literals_str + " ∧ " + futures_str + ")"
            else:
                res += " v " + "(" + literals_str + " ∧ " + futures_str + ")"
            
        return res

def leer_fichero():

        path = sys.argv[1]
        mode = 1
        if len(sys.argv) == 3:
            mode = sys.argv[2]
        with open(path, 'r') as f:
            parseFormulas = ['&', 'True']
            for formulaStr in f:
                if formulaStr == "\n" or formulaStr=="":
                    continue
                formulaStr = formulaStr.replace("\n", "").replace(" ", "")
                formula_ab = TemporalFormula(formulaStr).ab
                parseFormulas.append(formula_ab)

            f.close()  
            return parseFormulas, mode

def ejecute():
    parseFormulas, mode = leer_fichero()
    models = prime_cover_via_BICA(parseFormulas)
    post_processing_models = post_processing_bica_models(models)
    print("DNF: ", print_formula(post_processing_models))
    tnf = TNF(post_processing_models).tnfStr
    print("TNF: ", tnf)

    
    
def post_processing_bica_models(models):
    processing_models = []
    for model in models:
        literals = set()
        futures = set()
        for l in list(model):
            if "X" in l or "F[" in l or "G[" in l:
                futures.add(l)
            else:
                literals.add(l)
        processing_models.append([literals, [futures]])
    return processing_models


ejecute()
