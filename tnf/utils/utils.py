from asyncio import futures
from os import remove
from temporal_formula import TemporalFormula
from z3 import *
from tools import MiniSAT
from circuit import Circuit


def get_neg_literal(literal):
    first_char = literal[0]
    if first_char in ['-', '!']:
        return literal[1:]
    else:
        return "-" + literal

def get_variable(literal):
    if literal[0] == "-":
        return literal[1:]
    else:
        return literal
def is_neg(op):
    return ((op == "!") or (op == "-") or (op == "~"))

def is_and(op):
    return (op == "&&") or (op == "&")

def is_or(op):
    return (op == "||") or (op == "|")

def is_next(op):
    return op == "X"

def is_next_formula(formula):
    return formula[0] == "X"

def is_eventually(formula):
    return "F[" in formula 

def is_var_env(var):
    return len(var) > 2 and var[-2:] == "_e" 

def is_true(formula):
    return isinstance(formula, str) and (formula == "T" or formula == "True")

def is_false(formula):
    return isinstance(formula, str) and (formula == "F" or formula == "False")

def is_unary(formula):
    return isinstance(formula, list) and len(formula) == 2

def is_binary(formula):
    return isinstance(formula, list) and len(formula) == 3

def is_always(op):
    return "G[" in op
    
def is_variable(formula):
    return len(formula) == 1

def G_to_F(op):
    return op.replace('G', 'F')

def F_to_G(op):
    return op.replace('F', 'G')
    
def has_neg(formula):
    return "-" in formula

def delete_neg_str(formula):
    return formula.replace("-", "")

def is_temp_op(op):
    return (op == "X") or ("F" in op) or ("G" in op)

def delete_temp_ops(formula):
    if is_temp_op(formula[0]):
        return delete_temp_ops(formula[1])
    else:
        return formula

def neg_literal(strLiteral):
    if strLiteral[0] == "-":
        return strLiteral[1:]
    else:
        return "-" + strLiteral

def get_variable(formula):
    if is_temp_op(formula[0]):
        if is_eventually(formula):
            deleteEventuality = formula.split("]", 1)
            return get_variable(deleteEventuality[1])
        else:
            return get_variable(formula[1:])
    elif formula[0] == "-":
        return formula[1:]
    else :
        return formula

def is_atom(strFormula):
    return get_variable(strFormula) == strFormula


def to_str(formula):
    if isinstance(formula, str):
        return formula
    elif len(formula) == 2:
        if is_neg(formula[0]):
            return  formula[0] + to_str(formula[1])
        else:   
            return formula[0] + "(" + to_str(formula[1]) +")"
    else :
        leftFormula = to_str(formula[1])
        rightFormula = to_str(formula[2])
        return "(" + leftFormula + ")" + formula[0] + "(" + rightFormula + ")"

def count_next(formula):
    if is_next(formula[0]):
        return 1 +  count_next(formula[1])
    else:
        return 0


    
def get_temporal_op_limits(op):
    limitInf = ""
    limitSup = ""
    start = False
    end = False
    for f in op:

        if f == ",":
            start = False
            end = True
        elif f == "]":
            break
        elif f == "[":
            start = True
        elif start:
            limitInf = limitInf + f
        elif end: 
            limitSup = limitSup + f
        else: 
            continue
    return int(limitInf), int(limitSup)

def include_next_to_formula(formula):
    if formula[0] == 'G' or formula[0] =='F':
        formulaWithOutOp= formula.split("]")[1]
        limitInf, limitSup = get_temporal_op_limits(formula)
        newLimitInf = str(limitInf + 1)
        newLimitSup = str(limitSup + 1)
        return formula[0] + "[" +newLimitInf+","+newLimitSup+ "]"+formulaWithOutOp


    else:
        return 'X(' + formula + ")" 
    

def print_bica(formula):
    formulaStr = ""
    for f in formula:
        modelStr = ""
        print(f)
        for l in list(f):
            print(l)
            if modelStr == "":
                modelStr += l
            else:
                modelStr += " ∧ " + l
        if formulaStr == "":
                formulaStr += l
        else:
            formulaStr += " v " +l
    return formulaStr



def getStrToList(formulaStr):
    return TemporalFormula(formulaStr).ab

def get_literals(formula):
        if isinstance(formula, str):
            return {formula}
        elif len(formula) == 2:
            return get_literals(formula[1])
        else:
            res1 = get_literals(formula[1])
            res2 = get_literals(formula[2])
            return res1 | res2  

def is_temp_op(op):
    return (op == "X") or ("F" in op) or ("G" in op)

def delete_temp_ops(formula):
    if is_temp_op(formula[0]):
            return delete_temp_ops(formula[1])
    else:
        return formula


def get_temporal_limits(formula):
    limitInf = ""
    limitSup = ""
    start = False
    end = False
    cNext = count_next(formula)
    if is_atom(formula) or (formula[0] == "-" and is_atom(formula[1])):
        return int(0), int(0)
    if cNext > 0:
        return int(cNext), int(cNext)
    for f in formula[0]:

        if f == ",":
            start = False
            end = True
        elif f == "]":
            break
        elif f == "[":
            start = True
        elif start:
            limitInf = limitInf + f
        elif end: 
            limitSup = limitSup + f
        else: 
            continue
    return int(limitInf), int(limitSup)
     

def is_in_interval_success(phiAb, alphaAb):
    n, m = get_temporal_limits(alphaAb)
    nprima, mprima = get_temporal_limits(phiAb)
    if not is_always(phiAb[0]):
        if not is_always(alphaAb[0]):
            return (nprima >= n and nprima <= m) and (mprima >= n and mprima <= m)
        else:
            return n == m and mprima == nprima and n == nprima
    else:
       return (n >= nprima and nprima <= m) and (n <= mprima and mprima >= m)


def post_processing_bica_models(models, subsumptions):
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
                    if subsumes(fi, l, subsumptions):
                        break
                    elif subsumes(l, fi, subsumptions):
                        for fj in list(futures):
                            if subsumes(l, fj, subsumptions):
                                delete_futures.add(fj)
                        
                        futures.add(l)
                        break
                    else:
                        futures.add(l)
                futures = futures - delete_futures
                       
            else:
                literals.add(l)
        if futures == set():
            futures = {"True"}
        processing_models.append([literals, [futures]])
    return processing_models


def subsumes(future1, future2, subsumptions = None):
    #future1 subsumes future2
    if subsumptions:
        return future2 in subsumptions[future1]

    if future1 == future2:
        return True

    if future1[0] == "X":
        future1 = include_next_to_formula(future1[1:])

    if future2[0] == "X":
        future2 = include_next_to_formula(future2[1:])

    future1List = getStrToList(future1)
    future1Literals = get_literals(future1List)

    future2List = getStrToList(future2)

    future2Literals = get_literals(future2List)

    if future1Literals >= future2Literals and is_in_interval_success(future1List, future2List):
            if is_in_interval_success(future1List, future2List):
                literal1WithOutTemp = delete_temp_ops(future1List)
                literal2WithOutTemp = delete_temp_ops(future2List)
                f = ['&', literal1WithOutTemp, ['-', literal2WithOutTemp]]
                C = Circuit()
                C.list_to_circ(f)
                C.write_in_DIMACS("pos.cnf", add_BICA_line=True)
                if not (MiniSAT("pos.cnf") == "SAT"):
                    remove("pos.cnf")
                    return True
                    
    return False

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


def get_X(separated_formulas):
    X = set()
    for separated_formula in separated_formulas:
        for l in separated_formula[0]:
            if is_var_env(l):
                if l[0] == "-":
                    X.add(l[1:])
                else:
                    X.add(l)
    return X


def print_subsumptions(s):
    for key in s.keys():
        print(" ", key, " subsumes ", s[key])


def is_valid_model(model):
    modelAux = list(model)
    while modelAux:
        l = modelAux.pop()
        if l[0] == "-" :
            lneg = l[1:]
        else:
            if is_always(l) or is_eventually(l):
                lneg = TemporalFormula("-"+l).str
                
            else:
                lneg = "-" + l
        for lm in modelAux:
            if subsumes(lm, lneg):
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
                    res += OR + "(" + futures_str + ")"
                elif futures_str == "":
                    res += OR + "(" + literals_str  + ")"
                else:
                    res += OR + "(" + literals_str + AND + futures_str + ")"
            res += "\n"
            
        return res

def is_dnf_equal_tnf(dnf, tnf):
    negTNF_ab = neg_separated_formulas_to_ab(tnf)
    negDNF_ab = neg_separated_formulas_to_ab(dnf)
    tnf_ab = separated_formulas_to_ab(tnf)
    dnf_ab = separated_formulas_to_ab(dnf)
    f1toAB = ['&', dnf_ab, negTNF_ab]
    f2toAB = ['&', tnf_ab, negDNF_ab]
    
    C = Circuit()
    C.list_to_circ(f1toAB)
    C.write_in_DIMACS("pos.cnf", add_BICA_line=True)
    if not (MiniSAT("pos.cnf") == "SAT"):
        remove("pos.cnf")
    else:
        return False
    C = Circuit()
    C.list_to_circ(f2toAB)
    C.write_in_DIMACS("pos.cnf", add_BICA_line=True)
    if not (MiniSAT("pos.cnf") == "SAT"):
        remove("pos.cnf")
    else:
        return False
    return True

def is_stnf_implies_tnf(tnf, stnf):

    negTNF_ab = neg_separated_formulas_to_ab(tnf)
    stnf_ab = separated_formulas_to_ab(stnf)
    f1toAB = ['&', stnf_ab, negTNF_ab]
    
    C = Circuit()
    C.list_to_circ(f1toAB)
    C.write_in_DIMACS("pos.cnf", add_BICA_line=True)
    if not (MiniSAT("pos.cnf") == "SAT"):
        remove("pos.cnf")
        return True
    else:
        return False

def neg_separated_formulas_to_ab(separated_formulas):
    neg_to_ab = ['&']
    for separated_formula in separated_formulas:
        neg_to_ab.append(neg_separated_formula_to_ab(separated_formula))
    return neg_to_ab

def separated_formulas_to_ab(separated_formulas):
    to_ab = ['|']
    for separated_formula in separated_formulas:
        to_ab.append(separated_formula_to_ab(separated_formula))
    return to_ab

def neg_separated_formula_to_ab(separated_formula):
    literals = separated_formula[0]
    futures = separated_formula[1]
    separated_formula_ab = ['|', 'False', 'False']
    for literal in literals:
        separated_formula_ab.append(simple_negation_ab(literal))
    neg_futures = ['&', 'True', 'True']
    for future in futures:
        neg_future_i = ['|', 'False', 'False']
        for f in future:
            neg_future_i.append(simple_negation_ab(f))
        neg_futures.append(neg_future_i)
    separated_formula_ab.append(neg_futures)

    return separated_formula_ab

def separated_formula_to_ab(separated_formula):
    literals = separated_formula[0]
    futures = separated_formula[1]
    separated_formula_ab = ['&', 'True', 'True']
    for literal in literals:
        separated_formula_ab.append(simple_formula_ab(literal))
    neg_futures = ['|', 'False', 'False']
    for future in futures:
        neg_future_i = ['&', 'True', 'True']
        for f in future:
            neg_future_i.append(simple_formula_ab(f))
        neg_futures.append(neg_future_i)
    separated_formula_ab.append(neg_futures)
    return separated_formula_ab

def simple_negation_ab(l):
    if l == "True":
        return "False"
    if l == "False":
        return "True"
    if l[0] == "-":
        return l[1:]
    else:
        return ['-', l]

def simple_formula_ab(f):
    if f[0] == "-":
        return ['-', f[1:]]
    else:
        return f




