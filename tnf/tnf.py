
import copy
import csv
from doctest import SKIP
from hashlib import new
from http.cookiejar import CookiePolicy
import itertools
from operator import index
from os import remove
import random
import sys
import time

from numpy import short

from utils import utils
from temporal_formula import TemporalFormula
from run_bica import prime_cover_via_BICA
from collections import deque

class TNF:
    def __init__(self, formula, env_vars, subsumptions, flines = False, info = dict()):
        self.__set_initial_parameters(formula, env_vars, subsumptions, info)
        self.calculate_stnf()
        self.calculate_tnf()
        #self.calculate_verifications()
        if flines:
           self.info['Lines'] = flines
           self.calculate_analysis()
        self.__print_info()
        self.__print_tnf()
        self.__print_stnf()
        


    def __set_initial_parameters(self, formula, env_vars, subsumptions, info):
        self.formula = formula
        self.info = info
        self.env_vars = env_vars
        self.subsumptions = subsumptions
        self.i = 0
        self.cv = 0
        self.copy = 0


    def calculate_weakest(self):
        self.weakest_tnf = self.weakest_sf(self.tnfFormula)
        self.weakest_stnf = self.weakest_sf(self.short_tnf_res)
        self.equal_weakest_tnf_stnf = self.__are_equal_sf(self.weakest_tnf, self.weakest_stnf)
        self.__add_info("EQUAL WEAKEST", self.equal_weakest_tnf_stnf)


    def __are_equal_sf(self, sf1, sf2):
        for sf1_i in sf1:
            sf1_i_l = sf1_i[0]
            sf1_i_f = sf1_i[1]
            sf_i_equal = False
            for sf2_i in sf1:
                sf2_i_l = sf2_i[0]
                sf2_i_f = sf2_i[1]
                if sf1_i_l == sf2_i_l and self.__are_strict_equal_sf_futures(sf1_i_f, sf2_i_f):
                    sf_i_equal = True
                    break
            if not sf_i_equal:
                return False
        return True
                    
                    
    def __are_strict_equal_sf_futures(self, f1, f2):
        if len(f1) != len(f2):
            return False
        for f1_i in f1:
            if f1_i not in f2:
                return False
        return True
                
                

    def calculate_tnf(self):
        start = time.time()
        self.tnfFormula = self.tnf()
        self.__add_time(start, "TNF(s)")
        self.__add_info("TNF Length", len(self.tnfFormula))
        
    def calculate_stnf(self):
        start = time.time()
        self.short_tnf_res = self.short_tnf()
        self.__add_time(start, "STNF(s)")
        self.__add_info("STNF Length", len(self.short_tnf_res))


        
        

    def calculate_verifications(self):
        start = time.time()
        self.is_dnf_equal_tnf = utils.is_dnf_equal_tnf(self.formula, self.tnfFormula)
        self.is_stnf_implies_tnf = utils.is_stnf_implies_tnf(self.tnfFormula, self.short_tnf_res)

        self.__add_time(start, "VERIFICATION(s)")
        self.__add_info("DNF = TNF",  self.is_dnf_equal_tnf)
        self.__add_info("STNF => TNF",  self.is_stnf_implies_tnf)

    def __print_tnf(self):
        print("\n########################### TNF ###########################\n")
        print(utils.print_separated_formula(self.tnfFormula))
        print("\n########################### TNF ###########################\n")

    def __print_stnf(self):
        print("\n########################### STNF ###########################\n")
        print(utils.print_separated_formula(self.short_tnf_res))
        print("\n########################### STNF ###########################\n")




    def __print_info(self):
        print("########################### INFO ###########################\n")
        for key, value in self.info.items():
            print(">>", key, ": ", value, "\n")
        print("########################### INFO ###########################")
    def calculate_analysis(self):
        with open("analysis_TNF.csv", 'a') as f:
            w = csv.DictWriter(f, self.info.keys())
            #w.writeheader()
            w.writerow(self.info)
        #self.__write_csv(flines, len(self.formula), self.tnf_time, len(self.tnfFormula), self.short_tnf_time, len(self.short_tnf_res), self.dnf_tnf_verification, self.tnf_to_stnf_verification, "analysis_TNF.csv")

    def __write_csv(self, f, DNF_len, TNF_Time, TNF_length, sTNF_time, sTNF_length, TNF_equal_DNF, sTNF_implies_TNF, path):

        row =  [f, DNF_len, TNF_Time, TNF_length, sTNF_time, sTNF_length, TNF_equal_DNF, sTNF_implies_TNF]
        # open the file in the write mode
        with open(path, mode='a') as f:
            writer = csv.writer(f, delimiter=',')
            # write a row to the csv file
            writer.writerow(row)

        # close the file
        f.close()

    def __add_info(self, key, value):
        self.info[key] = value

    def __add_time(self, start, strTime):
        s = time.time()-start
        self.__add_info(strTime, round(s, 6))
        self.currentTime = time.time() 

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

    def __dnf_literals(self, d, di, negdj, future, all = True):
        if all:
            return self.__dnf_literals_all(d, di, negdj, future)
        else:
            return self.__dnf_literals_alternative(d, di, negdj, future)


    def __dnf_literals_all(self, d, di, negdj, future):
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

    def __dnf_literals_alternative(self, d, di, negdj, future):
        if negdj == set():
            return False
        res = list()
    
        for literal in list(negdj):
            neg_literal = {utils.neg_literal(literal)}
            res.append([d.union(di).union(neg_literal), future])
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
        if future_formulas_i == [{"True"}]:
            future_formulas_i = [set()]
        if future_formulas_j == [{"True"}]:
            future_formulas_j = [set()]
        new_join_2 = self.__dnf_literals(d, d1, d2, future_formulas_i)
        new_join_3 = self.__dnf_literals(d, d2, d1, future_formulas_j)
        return new_join_1, new_join_2, new_join_3
            
    def __join_futures(self, future1, future2):
        if future1 == [set()] or future2 == [set()]:
            return [set()]
        if future1 == [{"True"}] or future2 == [{"True"}]:
            return [set()]
        join_f = copy.copy(future1)
        for f2 in future2:
            added = False
            for f1 in future1:
                if f1 > f2 and f1 != set() and f2 != set():
                    if f1 in join_f:
                        join_f.remove(f1)
                    join_f.append(f2)
                    added = True
                elif f1 == f2:
                    added = True
                else:
                    continue
            if not added and f2!= set():    
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
                        break
                if changed:
                    break
            if not changed:
                all_hold_condition = True
        return formula

    def __futures_set_subsumption(self, set1, set2):
        if set1 == {'True'}:
            return False
        for future1 in set1:
            for future2 in set2:
                if not (future2 in self.subsumptions[future1]):
                    return False
        return True
    
    def weakest_sf(self, separated_formulas):
        res = list()
        for sf_i in separated_formulas:
            sf_i_env_literals = self.__delete_system_vars(sf_i[0])
            sf_i_futures = sf_i[1]

            added = False
            for sf_j in res:
                sf_j_env_literals = sf_j[0]
                sf_j_futures = sf_j[1]
                if sf_i_env_literals <= sf_j_env_literals and self.are_all_futures_in(sf_j_futures, sf_i_futures):
                    res.remove(sf_j)
                    res.append([sf_i_env_literals, sf_i_futures])
                    added = True
                    break
                if sf_j_env_literals <= sf_i_env_literals and self.are_all_futures_in(sf_i_futures, sf_j_futures):
                    added = True
                    break
            if not added:
                res.append([sf_i_env_literals, sf_i_futures])
        return res

    def are_all_futures_in(self, f1, f2):
        #f1 in f2
        for f1_i in f1:
            if f1_i not in f2:
                return False
        return True         

    def __delete_system_vars(self, literals):
        res = set()
        for l in literals:
            if utils.is_var_env(l):
                res.add(l)
        return res
    
    def __append_future(self,union_futures, futures_i):
        if union_futures == [{'True'}] or futures_i == {'False'}:
            return
        remove_futures = list()
        futures_i_subsumed = False
        for union_futures_i  in union_futures:
            if self.__futures_set_subsumption(union_futures_i, futures_i):
                futures_i_subsumed = True
                break
            if self.__futures_set_subsumption(futures_i, union_futures_i):
                remove_futures.append(union_futures_i)
        if not futures_i_subsumed:
            for remove_futures_i in remove_futures:
                union_futures.remove(remove_futures_i)
            union_futures.append(futures_i)

    def __symmetric_consistent_difference(self, set1, set2):
        for elem1 in set1:
            neg_elem1 = utils.neg_literal(elem1)
            if neg_elem1 in set2:
                return False
        return set1.symmetric_difference(set2)

    def __short_tnf_step(self, env_var_assigment,formula, short_tnf, skip):

        literals_stack = deque()
        futures_stack = deque()
        index_stack = deque()
        literals_stack.append(env_var_assigment)
        futures_stack.appendleft([{'False'}])
        index_stack.append(0)

        i = index_stack[0]
        while index_stack and futures_stack and literals_stack:
            print(len(short_tnf))
            self.i+=1
            literals_i, futures_i = formula[i][0], formula[i][1]
            current_l = literals_stack[0]
            current_f = futures_stack[0]
            start = time.time()
            diff_literals = current_l.symmetric_difference(literals_i)
            self.cv += time.time() - start
            if self.__is_consistent(diff_literals):
                start = time.time()
                union_literals = current_l.union(literals_i)
                self.cv += time.time() - start
                if self.__not_visited(union_literals, skip):
                
                    if union_literals != current_l:
                        literals_stack.appendleft(union_literals)
                        if current_f != [{'False'}]:  
                            start = time.time()  
                            union_futures = copy.deepcopy(current_f)
                            self.copy+=time.time()-start
                            self.__append_future(union_futures, futures_i[0])
                            futures_stack.appendleft(union_futures)
                        else:
                            futures_stack.appendleft([futures_i[0]])
                        if i < (len(formula) - 2):
                            index_stack.appendleft(i+1)
                        
                    else:
                        if futures_i == [set()]:
                            futures_stack = deque()
                            futures_stack.appendleft([{'True'}])
                        elif current_f != [{'False'}]:
                            self.__append_future(current_f, futures_i[0])
                        else:
                            futures_stack.popleft()
                            futures_stack.appendleft([futures_i[0]])
            i += 1            
            
            if i == len(formula) and index_stack:
                i = index_stack.popleft()  
                move_literals = literals_stack.popleft()
                move_futures = futures_stack.popleft()
                move = [move_literals, move_futures]
                self.__insert_to_short_tnf2(move, short_tnf)
                #print(move)
                # if self.__not_visited(move_literals, skip) and move_futures != [{'False'}]:
                #     move = [move_literals, move_futures]
                #     self.__insert_to_short_tnf(move, short_tnf)
                #     skip.append(move_literals)


    def short_tnf(self):
        short_tnf = list()
        skip = list()
        if not self.env_vars:
            self.__short_tnf_step(set(),self.formula, short_tnf, skip)
        for env_var in list(self.env_vars):
            not_env_var = utils.neg_literal(env_var)     
            self.__short_tnf_step({env_var},self.formula, short_tnf, skip)
            print(len(short_tnf))
            self.__short_tnf_step({not_env_var},self.formula, short_tnf, skip)
            print(len(short_tnf))
        return short_tnf


        


    def __insert_to_short_tnf(self, new_move, short_tnf):
        if new_move in short_tnf:
            return
        if [{"True"}] == new_move[1]:
            new_move[1] = [set()]
        remove_list = list()
        subsumed = False
        for move in short_tnf:
            if move[0] == new_move[0] or move[0] > new_move[0] or move[0] < new_move[0]:
                if self.__has_weaker_futures(move, new_move):
                    subsumed = True
                    break

                if self.__has_weaker_futures(new_move, move):
                    remove_list.append(move)
        if not subsumed:
            for m in remove_list:
                short_tnf.remove(m)
            short_tnf.append(new_move)

    def __insert_to_short_tnf2(self, new_move, short_tnf):
        if new_move in short_tnf:
            return
        if [{"True"}] == new_move[1]:
            new_move[1] = [set()]
        remove_list = list()
        subsumed = False
        for move in short_tnf:
            if move[0] == new_move[0] or move[0] > new_move[0]:
                if self.__has_weaker_futures(new_move, move):
                    remove_list.append(move)
            if move[0] < new_move[0]:
                if self.__has_weaker_futures(move, new_move):
                    subsumed = True
                    break

        if not subsumed:
            for m in remove_list:
                short_tnf.remove(m)
            short_tnf.append(new_move)
        


        
    def __has_weaker_futures(self, move1, move2):
        if move1 == move2:
            return True
        for future_2_i in move2[1]:
            subsumed = False
            for future_1_i in move1[1]:
                if self.__futures_set_subsumption(future_1_i, future_2_i):
                    subsumed  = True
                    break
            if not subsumed:
                return False
        return True


    def __not_visited(self, a, l):
        start = time.time()
        for e in l:
            if a >= e:
                self.cv += time.time() - start
                return False
        self.cv += time.time() - start
        return True

    def __is_consistent(self, formula):
        start = time.time()
        for l in list(formula):
            not_l = utils.neg_literal(l)
            if not_l in formula:
                self.cv += time.time() - start
                return False
        self.cv += time.time() - start
        return True

                

def automatic_benchmark_generator(n):
    path = "benchmarks/all_formulas.txt"
    
    with open(path, 'r') as f:
            parseFormulas = ['&', 'True']
            formulasStr = "(True)"
            nline = 1
            validLines = random.sample(range(1, 370), n)
            validLines = [84, 9, 136, 44]
            print("Lineas: ", validLines)
            for formulaStr in f:
                if nline in validLines:
                    if formulaStr == "\n" or formulaStr=="":
                        continue
                    formulaStr = "&("+formulaStr.replace("\n", "").replace(" ", "")+")"
                    formulasStr+=formulaStr
                nline+=1

            formula = TemporalFormula(formulasStr)
            formula_ab = formula.ab
            parseFormulas.append(formula_ab)
    f.close()  
    return parseFormulas, validLines



def leer_fichero():
        if len(sys.argv) == 1:
            path = "tnf/benchmarks/Overleaf/bench2"
        else:
            path = sys.argv[1]
        mode = 1
        if len(sys.argv) == 3:
            mode = sys.argv[2]
        with open(path, 'r') as f:
            parseFormulas = ['&', 'True']
            formulasStr = "(True)"
            for formulaStr in f:
                if formulaStr == "\n" or formulaStr=="":
                    continue
                formulaStr = "&("+formulaStr.replace("\n", "").replace(" ", "")+")"
                formulasStr+=formulaStr

            formula = TemporalFormula(formulasStr)
            formula_ab = formula.ab
            parseFormulas.append(formula_ab)

        f.close()  
        return parseFormulas

def ejecute(automatic = False):
    
    info = dict()
    validLines = False
    if automatic:
        parseFormulas, validLines = automatic_benchmark_generator(4)
    else:
        parseFormulas = leer_fichero()
    start = time.time()
    #print(parseFormulas)
    models = prime_cover_via_BICA(parseFormulas)
    info['BICA(s)'] = round(time.time()-start, 6) 
    #print("\nDNF BICA (", time.time() - start, "s) :\n", len(models), models)
    start = time.time()
    subsumptions = utils.calculate_subsumptions(models)
    info['SUBSUMPTIONS(s)'] = round(time.time()-start, 6) 
    #print("\nSUBSUMPTIONS: (", time.time() - start, "s) :\n")
    #utils.print_subsumptions(subsumptions)
    start = time.time()
    post_processing_models = utils.post_processing_bica_models(models, subsumptions)
    info['PÔST-PROCESSING MODELS(s)'] = round(time.time()-start, 6) 
    
    env_vars = utils.get_X(post_processing_models)
    print(env_vars)
    info['ENV VARS'] = len(env_vars)
    info['MODELS'] = len(post_processing_models)

    #print("\nPOSTPROCESSING DNF (", time.time() - start, "s) :\n", utils.print_separated_formula(post_processing_models))
    
    TNF(post_processing_models, env_vars, subsumptions, validLines, info)
    if automatic:
        ejecute()


ejecute()