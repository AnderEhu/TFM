from temporal_formula import TemporalFormula
from z3 import *

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

def is_enum(op):
    return (op == "==") or (op == "=")

def is_eventually(formula):
    return "F[" in formula 

def is_var_env(var):
    return len(var) > 2 and var[-2:] == "_e" 

def is_true(formula):
    return isinstance(formula, str) and (formula == "T" or formula == "True")

def is_false(formula):
    return isinstance(formula, str) and (formula == "F" or formula == "False")


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
def has_connective(formula):
    return ("&" in formula) or ("|" in formula)

def neg_literal(strLiteral):
    if strLiteral[0] == "-":
        return strLiteral[1:]
    else:
        return "-" + strLiteral

def is_neg_xnnf(formula):
    return "-" in formula

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

def has_negation(strFormula):
    if is_atom(strFormula):
        return False
    elif neg_literal(strFormula):
        return True
    else:
        return has_negation(strFormula[1:])

def neg_literal_xnnf(formula):
    if isinstance(formula, str):
        return neg_literal(formula)
    elif formula[0] == "-":
        return formula[1]
    else:
        rightFormula = neg_literal_xnnf(formula[1])
        return formula[0] + rightFormula

def neg_literal_xnnf_str(formula):
    if is_neg(formula[0]):
        return formula[1:]
    elif is_temp_op(formula[0]):
        return formula[0] + neg_literal_xnnf_str(formula[1:])
    else:
        return neg_literal(formula)

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

def to_z3(formula):
    if isinstance(formula, str):
        if is_true(formula):
            return True
        elif is_false(formula):
            return False
        elif formula[0] == "-":
            return Not(Bool(formula[1:]))
        else:
            return Bool(formula)
    elif isinstance(formula, list) and len(formula) == 1:
        return to_z3(formula[0])
    elif len(formula) == 2:
        if is_neg(formula[0]):
            subformula = to_z3(formula[1])
            return Not(subformula)
        elif is_eventually(formula[0]) or is_always(formula[0]) : #Corregir
            return Bool(to_str(formula))
        else: #Next
            subformula = to_z3(formula[1])
            strFormula =to_str(formula)
            if has_neg(strFormula):
                strFormulaSinNeg = delete_neg_str(strFormula)
                return Not(Bool(strFormulaSinNeg))
            else:
                return Bool(strFormula)

    elif formula[0] == "->":
        leftFormula = to_z3(formula[1])
        rightFormula = to_z3(formula[2])
        return Implies(leftFormula, rightFormula)

    else:
        subFormulasZ3 = list()
        for subformula in formula[1:]:
            subFormulasZ3.append(to_z3(subformula))
        if is_or(formula[0]): 
            return Or(subFormulasZ3)
        if is_and(formula[0]):
            return And(subFormulasZ3)


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