
from ast import parse
from asyncio import futures
import copy
from ctypes import util
from hashlib import new
import itertools
from operator import index
import sys
import time
from z3 import *

from numpy import copyto
from utils import utils
from temporal_formula import TemporalFormula
from run_bica import prime_cover_via_BICA
from collections import deque

class TNF:
    def __init__(self, formula, env_vars, subsumptions):
        self.formula = formula
        self.env_vars = env_vars
        self.subsumptions = subsumptions
        start = time.time()
        self.short_tnf_res = self.short_tnf()
        self.short_tnfStr = print_separated_formula(self.short_tnf_res)
        print("\nShort TNF (", time.time() - start, "s) :\n", self.short_tnfStr, "")
        start = time.time()
        self.weakest_short_tnf = self.short_tnf(True)
        self.weakest_short_tnfStr = print_separated_formula(self.weakest_short_tnf)
        print("\nWeakest Short TNF (", time.time() - start, "s) :\n", self.weakest_short_tnfStr, "")
        start = time.time()
        self.tnfFormula = self.tnf()
        self.tnfStr = print_separated_formula(self.tnfFormula)
        print("\nTNF (", time.time() - start, "s) :\n", self.tnfStr, "")
        


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
                if f1 > f2 and f1 != set():
                    if f1 in join_f:
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
                        #print("\n Formula: ",  print_separated_formula(formula))
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
                        #print("\n No cumple condicion, genera: ",print_separated_formula(formula))
                        break
                    #else:
                        #print("\n Cumple condicion")
                if changed:
                    break
            if not changed:
                all_hold_condition = True
        return formula

    def set_subsumption(self, set1, set2):
        for future1 in set1:
            for future2 in set2:

                if not (future2 in self.subsumptions[future1]):
                    return False

        return True
    
    def append_future(self,union_futures, futures_i):
        union_futures_aux= copy.deepcopy(union_futures)
        for union_futures_i  in union_futures_aux:
            if self.set_subsumption(union_futures_i, futures_i):
                return
            if self.set_subsumption(futures_i, union_futures_i):
                union_futures.remove(union_futures_i)
        union_futures.append(futures_i)

    def short_tnf_step(self, env_var_assigment, short_tnf, weakest):
        literals_stack = deque()
        futures_stack = deque()
        index_stack = deque()

        literals_stack.append(env_var_assigment)
        futures_stack.appendleft([{'XFalse'}])
        index_stack.append(0)

        i = index_stack[0]
        skip = list()

        while index_stack:
            literals_i, futures_i = self.formula[i][0], self.formula[i][1]
            current_l = literals_stack[0]
            current_f = futures_stack[0]
            diff_literals = current_l.symmetric_difference(literals_i)
            union_literals = current_l.union(literals_i)

            if self.is_consistent(diff_literals) and self.not_visited(union_literals, skip):
                if union_literals != current_l:
                    literals_stack.appendleft(union_literals)
                    if current_f != [{'XFalse'}]:    
                        union_futures = copy.deepcopy(current_f)
                        #union_futures.append(futures_i[0])
                        self.append_future(union_futures, futures_i[0])
                        futures_stack.appendleft(union_futures)
                    else:
                        futures_stack.appendleft([futures_i[0]])
                    if i < (len(self.formula) - 2):
                        index_stack.appendleft(i+1)
                    
                else:
                    if current_f != [{'XFalse'}]:
                        self.append_future(current_f, futures_i[0])
                    else:
                        futures_stack.popleft()
                        futures_stack.appendleft([futures_i[0]])
            i += 1            
            
            if i == len(self.formula) and index_stack:
                i = index_stack.popleft()  
                move_literals = literals_stack.popleft()
                move_futures = futures_stack.popleft()
                if self.not_visited(move_literals, skip) and move_futures != [{'XFalse'}]:
                    move = [move_literals, move_futures]
                    self.insert_to_short_tnf(move, short_tnf, weakest)
                    skip.append(move_literals)


    def short_tnf(self, weakest = False):
        short_tnf = list()
        
        if not self.env_vars:
            self.short_tnf_step(set(), short_tnf, weakest)
        for env_var in list(self.env_vars):
            
            not_env_var = utils.neg_literal(env_var)
            self.short_tnf_step({env_var}, short_tnf, weakest)
            self.short_tnf_step({not_env_var}, short_tnf, weakest)

        return short_tnf

    def insert_to_short_tnf(self, new_move, short_tnf, weakest):
        if weakest:
            short_tnf_aux = copy.deepcopy(short_tnf)
            for move in short_tnf_aux:
                move_env = self.get_env_vars(move[0])
                new_move_env = self.get_env_vars(new_move[0])
                    
                if move_env == new_move_env:
                    if self.list_set_subsumtion(move, new_move):
                        return

                    if self.list_set_subsumtion(new_move, move):
                        short_tnf.remove(move)
                
                if move_env > new_move_env:
                    if self.list_set_subsumtion(move, new_move):
                        return

                    if self.list_set_subsumtion(new_move, move):
                        short_tnf.remove(move)


                if move_env < new_move_env:
                    if self.list_set_subsumtion(move, new_move):
                        return

                    if self.list_set_subsumtion(new_move, move):
                        short_tnf.remove(move)
    
        short_tnf.append(new_move)

        
    def list_set_subsumtion(self, move1, move2):
        for future_2_i in move2[1]:
            subsumed = False
            for future_1_i in move1[1]:
                if self.set_subsumption(future_1_i, future_2_i):
                    subsumed  = True
                    break
            if not subsumed:
                return False
        return True

            
            


    def get_env_vars(self, s):
        env = set()
        for l in list(s):
            if  len(l) > 2 and l[-2:] == "_e":
                env.add(l)
        return env


    def not_visited(self, a, l):
        for e in l:
            if a >= e:
                return False
        return True

    def is_consistent(self, formula):
        for l in list(formula):
            not_l = utils.neg_literal(l)
            if not_l in formula:
                return False
        return True

                
            
            
    





def print_separated_formula(formula, AND = " ∧ ", OR = " v "):
        res = ""
        for fi in formula:
            literal_fi = fi[0]
            futures_fi = fi[1]
            literals_str = ""
            for li_fi in list(literal_fi):
                if literals_str == "":
                    literals_str += li_fi
                else:
                    literals_str += AND +li_fi
            futures_str = ""
            for futuresi_fi in futures_fi:
                and_futures_ij = ""
                for futuresij_fi in futuresi_fi:
                    if and_futures_ij == "":
                        and_futures_ij = futuresij_fi
                    else:
                        and_futures_ij += AND +futuresij_fi

                if futures_str == "":
                    futures_str = and_futures_ij
                else:
                    futures_str = "(" + futures_str + ")" +  OR + "(" + and_futures_ij + ")"
            
            futures_str = "(" + futures_str + ")"
            
            
            if res == "":
                if literals_str ==  "":
                    res += futures_str
                elif futures_str == "":
                    res += "(" + literals_str  + ")"
                else:
                    res += "(" + literals_str + AND + futures_str + ")"
            else:
                if literals_str ==  "":
                    res += OR + futures_str
                elif futures_str == "":
                    res += OR + "(" + literals_str  + ")"
                else:
                    res += OR + "(" + literals_str + AND + futures_str + ")"
            
        return res

def leer_fichero():
        if len(sys.argv) == 1:
            path = "tnf/benchmarks/bench2"
        else:
            path = sys.argv[1]
        mode = 1
        if len(sys.argv) == 3:
            mode = sys.argv[2]
        env_vars = set()
        with open(path, 'r') as f:
            parseFormulas = ['&', 'True']
            for formulaStr in f:
                if formulaStr == "\n" or formulaStr=="":
                    continue
                formulaStr = formulaStr.replace("\n", "").replace(" ", "")
                formula = TemporalFormula(formulaStr)
                formula_ab = formula.ab
                env_vars = env_vars.union(formula.now_e)
                parseFormulas.append(formula_ab)

            f.close()  
            return parseFormulas, env_vars, mode

def ejecute():
    parseFormulas, env_vars, mode = leer_fichero()
    start = time.time()
    models = prime_cover_via_BICA(parseFormulas)
    print("\nDNF BICA (", time.time() - start, "s) :\n", models)
    start = time.time()
    subsumptions = calculate_subsumptions(models)
    print("\nSUBSUMPTIONS: (", time.time() - start, "s) :\n")
    print_subsumptions(subsumptions)
    start = time.time()
    post_processing_models = post_processing_bica_models(models, subsumptions)
    print("\nPOSTPROCESSING DNF (", time.time() - start, "s) :\n", print_separated_formula(post_processing_models))
    TNF(post_processing_models, env_vars, subsumptions)

def print_subsumptions(s):
    for key in s.keys():
        print(" ", key, " subsumes ", s[key])
    
def calculate_subsumptions(formula):
    subsumptions = dict()
    futures = set()
    for formula_i in formula:
        for formula_ij in formula_i:
            if "X" in formula_ij or "F[" in formula_ij or "G[" in formula_ij:
                subsumptions[formula_ij] = {formula_ij}
                futures.add(formula_ij)
    for key in subsumptions.keys():
        for future in list(futures):
            future1 = copy.deepcopy(key)
            future2 = copy.deepcopy(future)
            if subsumes(future1, future2):
                subsumptions[key].add(future)
    return subsumptions

def subsumes(future1, future2, subsumtions = None):
    if subsumtions:
        return future2 in subsumtions[future1]
    if future1 == future2:
        return True

    if future1[0] == "X":
        future1 = utils.include_next_to_formula(future1[1:])

    if future2[0] == "X":
        future2 = utils.include_next_to_formula(future2[1:])

    future1List = utils.getStrToList(future1)
    future1Literals = utils.get_literals(future1List)

    future2List = utils.getStrToList(future2)

    future2Literals = utils.get_literals(future2List)

    if future1Literals >= future2Literals:


            literal1WithOutTemp = utils.delete_temp_ops(future1List)
            literal2WithOutTemp = utils.delete_temp_ops(future2List)
            literal1WithOutTempZ3 = utils.to_z3(literal1WithOutTemp)
            negliteral2WithOutTempZ3 =  utils.to_z3(['-', literal2WithOutTemp])
            
            #literal1List -> literal2List
            if utils.is_in_interval_success(future1List, future2List):
                s = Solver()
                s.add(And(literal1WithOutTempZ3, negliteral2WithOutTempZ3)) 
                if not (s.check() == sat):
                    return True
                    


    return False

def post_processing_bica_models(models, subsumtions):
    processing_models = []
    for model in models:
        literals = set()
        futures = set()
        for l in list(model):
            if "X" in l or "F[" in l or "G[" in l:
                if not futures:
                    futures.add(l)
                    continue
                delete_futures = set()
                for fi in list(futures):
                    if subsumes(fi, l, subsumtions):
                        break
                    elif subsumes(l, fi, subsumtions):
                        for fj in list(futures):
                            if subsumes(l, fj, subsumtions):
                                delete_futures.add(fj)
                        
                        futures.add(l)
                        break
                    else:
                        futures.add(l)
                futures = futures - delete_futures
                       
            else:
                literals.add(l)
        processing_models.append([literals, [futures]])
    return processing_models


ejecute()
