# Hint: from collections import deque
from typing import Deque
from Interface import *


# = = = = = = = QUESTION 1  = = = = = = = #


def consistent(assignment, csp, var, value):
    """
    Checks if a value assigned to a variable is consistent with all binary constraints in a problem.
    Do not assign value to var.
    Only check if this value would be consistent or not.
    If the other variable for a constraint is not assigned,
    then the new value is consistent with the constraint.

    Args:
        assignment (Assignment): the partial assignment
        csp (ConstraintSatisfactionProblem): the problem definition
        var (string): the variable that would be assigned
        value (value): the value that would be assigned to the variable
    Returns:
        boolean
        True if the value would be consistent with all currently assigned values, False otherwise
    """
    # TODO: Question 1
    for constraint in csp.binaryConstraints:
        if constraint.affects(var) == False:
            continue
        other_var = constraint.otherVariable(var)
        if assignment.isAssigned(other_var):
            if constraint.isSatisfied(value, assignment.assignedValues[other_var]) == False:
                # the constraint is broken
                return False
    # if no inconsistency
    return True

def recursiveBacktracking(assignment, csp, orderValuesMethod, selectVariableMethod, inferenceMethod):
    """
    Recursive backtracking algorithm.
    A new assignment should not be created.
    The assignment passed in should have its domains updated with inferences.
    In the case that a recursive call returns failure or a variable assignment is incorrect,
    the inferences made along the way should be reversed.
    See maintainArcConsistency and forwardChecking for the format of inferences.

    Examples of the functions to be passed in:
    orderValuesMethod: orderValues, leastConstrainingValuesHeuristic
    selectVariableMethod: chooseFirstVariable, minimumRemainingValuesHeuristic
    inferenceMethod: noInferences, maintainArcConsistency, forwardChecking

    Args:
        assignment (Assignment): a partial assignment to expand upon
        csp (ConstraintSatisfactionProblem): the problem definition
        orderValuesMethod (function<assignment, csp, variable> returns list<value>):
            a function to decide the next value to try
        selectVariableMethod (function<assignment, csp> returns variable):
            a function to decide which variable to assign next
        inferenceMethod (function<assignment, csp, variable, value> returns set<variable, value>):
            a function to specify what type of inferences to use
    Returns:
        Assignment
        A completed and consistent assignment. None if no solution exists.
    """
    # TODO: Question 1
    # check if the assignment is complete
    if assignment.isComplete(): return assignment
    # check if the assignment is fail
    # the next variable to assign: var
    var = selectVariableMethod(assignment, csp)
    if not var: return None
    inferences = set([])
    for value in orderValuesMethod(assignment, csp, var):
        if consistent(assignment, csp, var, value) == True:
            assignment.assignedValues[var] = value
            inferences = inferenceMethod(assignment, csp, var, value)
            if inferences is not None:
                result = recursiveBacktracking(
                    assignment, csp, orderValuesMethod, selectVariableMethod, inferenceMethod)
                if result is not None:
                    return result
                for infer in inferences:
                    assignment.varDomains[infer[0]] = infer[1]
        assignment.assignedValues[var] = None
        if inferences is not None:
            for infer in inferences:
                if len(assignment.varDomains[infer[0]]) > 1:
                    assignment.varDomains[infer[0]].remove(infer[1])
    return None


def eliminateUnaryConstraints(assignment, csp):
    """
    Uses unary constraints to eleminate values from an assignment.

    Args:
        assignment (Assignment): a partial assignment to expand upon
        csp (ConstraintSatisfactionProblem): the problem definition
    Returns:
        Assignment
        An assignment with domains restricted by unary constraints. None if no solution exists.
    """
    domains = assignment.varDomains
    for var in domains:
        for constraint in (c for c in csp.unaryConstraints if c.affects(var)):
            for value in (v for v in list(domains[var]) if not constraint.isSatisfied(v)):
                domains[var].remove(value)
                # Failure due to invalid assignment
                if len(domains[var]) == 0:
                    return None
    return assignment


def chooseFirstVariable(assignment, csp):
    """
    Trivial method for choosing the next variable to assign.
    Uses no heuristics.
    """
    for var in csp.varDomains:
        if not assignment.isAssigned(var):
            return var


# = = = = = = = QUESTION 2  = = = = = = = #


def minimumRemainingValuesHeuristic(assignment, csp):
    """
    Selects the next variable to try to give a value to in an assignment.
    Uses minimum remaining values heuristic to pick a variable. Use degree heuristic for breaking ties.

    Args:
        assignment (Assignment): the partial assignment to expand
        csp (ConstraintSatisfactionProblem): the problem description
    Returns:
        the next variable to assign
    """
    nextVar = None
    domains = assignment.varDomains

    # TODO: Question 2
    min_value_len = float('inf')
    for var in domains:
        if assignment.isAssigned(var) == True:
            # not consider assigned variables
            continue
        if len(domains[var]) < min_value_len:
            min_value_len = len(domains[var])
            nextVar = var
    return nextVar

def orderValues(assignment, csp, var):
    """
    Trivial method for ordering values to assign.
    Uses no heuristics.
    """
    return list(assignment.varDomains[var])


# = = = = = = = QUESTION 3  = = = = = = = #

def getConstraintCount(assignment, csp, value, var):
    count = 0
    for constraint in csp.binaryConstraints:
        if constraint.affects(var):
            other_var = constraint.otherVariable(var)
            if assignment.isAssigned(other_var):
                if constraint.isSatisfied(value, assignment.assignedValues[other_var]) == False:
                    # the constraint is broken, should not assign the corresponding value
                    count += 1
    return count

def leastConstrainingValuesHeuristic(assignment, csp, var):
    """
    Creates an ordered list of the remaining values left for a given variable.
    Values should be attempted in the order returned.
    The least constraining value should be at the front of the list.

    Args:
        assignment (Assignment): the partial assignment to expand
        csp (ConstraintSatisfactionProblem): the problem description
        var (string): the variable to be assigned the values
    Returns:
        list<values>
        a list of the possible values ordered by the least constraining value heuristic
    """
    # TODO: Question 3
    domains = assignment.varDomains
    count_list = []
    for value in domains[var]:
        count_list.append((getConstraintCount(assignment, csp, value, var), value))
    count_list.sort()
    values_list = []
    for x in count_list:
        values_list.append(x[1])
    return values_list



def noInferences(assignment, csp, var, value):
    """
    Trivial method for making no inferences.
    """
    return set([])


# = = = = = = = QUESTION 4  = = = = = = = #


def forwardChecking(assignment, csp, var, value):
    """
    Implements the forward checking algorithm.
    Each inference should take the form of (variable, value)
    where the value is being removed from the domain of variable.
    This format is important so that the inferences can be reversed
    if they result in a conflicting partial assignment.
    If the algorithm reveals an inconsistency,
    any inferences made should be reversed before ending the function.

    Args:
        assignment (Assignment): the partial assignment to expand
        csp (ConstraintSatisfactionProblem): the problem description
        var (string): the variable that has just been assigned a value
        value (string): the value that has just been assigned
    Returns:
        set< tuple<variable, value> >
        the inferences made in this call or None if inconsistent assignment
    """
    inferences = set([])

    # TODO: Question 4
    for constraint in (c for c in csp.binaryConstraints if c.affects(var)):
        other_var = constraint.otherVariable(var)
        remove_value_list = []
        if assignment.varDomains[other_var] is None:
            continue
        for other_value in assignment.varDomains[other_var]:
            if constraint.isSatisfied(value, other_value) == False:
                # remove the values that violate a constraint with the assignment
                remove_value_list.append(other_value)

        for remove_value in remove_value_list:
            if len(assignment.varDomains[other_var]) <= 1:
                # if the algorithm reveals an inconsistency: no variable left to assigned
                for infer in inferences:
                    assignment.varDomains[infer[0]].add(infer[1])
                # inferences in None if inconsistency occurs
                return None
            assignment.varDomains[other_var].remove(remove_value)
            inferences.add((other_var, remove_value))
            
    return inferences

# = = = = = = = QUESTION 5  = = = = = = = #


def revise(assignment, csp, var1, var2, constraint):
    """
    Helper function to maintainArcConsistency and AC3.
    Remove values from var2 domain if constraint cannot be satisfied.
    Each inference should take the form of (variable, value)
    where the value is being removed from the domain of variable.
    This format is important so that the inferences can be reversed
    if they result in a conflicting partial assignment.
    If the algorithm reveals an inconsistency,
    any inferences made should be reversed before ending the function.

    Args:
        assignment (Assignment): the partial assignment to expand
        csp (ConstraintSatisfactionProblem): the problem description
        var1 (string): the variable with consistent values
        var2 (string): the variable that should have inconsistent values removed
        constraint (BinaryConstraint): the constraint connecting var1 and var2
    Returns:
        set<tuple<variable, value>>
        the inferences made in this call or None if inconsistent assignment
    """
    inferences = set([])

    # TODO: Question 5
    for value1 in assignment.varDomains[var1]:
        res = False
        for value2 in assignment.varDomains[var2]: 
            if constraint.isSatisfied(value2, value1) == True:
                res = True
                break
        if res == False:
            # if revised
            # assignment.varDomains[var1].remove(value1)
            inferences.add((var1, value1))
    if len(assignment.varDomains[var1]) == len(inferences):
        # if after removing domains from assignment, assignment becomes empty
        # meaning that there is inconsistent assignment
        return None
    for infer in inferences:
        assignment.varDomains[infer[0]].remove(infer[1])
    return inferences




def maintainArcConsistency(assignment, csp, var, value):
    """
    Implements the maintaining arc consistency algorithm.
    Inferences take the form of (variable, value)
    where the value is being removed from the domain of variable.
    This format is important so that the inferences can be reversed
    if they result in a conflicting partial assignment.
    If the algorithm reveals an inconsistency,
    and inferences made should be reversed before ending the function.

    Args:
        assignment (Assignment): the partial assignment to expand
        csp (ConstraintSatisfactionProblem): the problem description
        var (string): the variable that has just been assigned a value
        value (string): the value that has just been assigned
    Returns:
        set<<variable, value>>
        the inferences made in this call or None if inconsistent assignment
    """
    inferences = set([])
    domains = assignment.varDomains

    # TODO: Question 5
    #  Hint: implement revise first and use it as a helper function"""
    queue = Deque()
    # initialize queue
    for constraint in (c for c in csp.binaryConstraints if c.affects(var)):
        other_var = constraint.otherVariable(var)
        if assignment.isAssigned(other_var) == False:
            # be careful with the order
            queue.append((other_var, var, constraint))

    while len(queue) > 0:
        vari, varj, constraint = queue.pop()
        inferences_tmp = revise(assignment, csp, vari, varj, constraint)
        if inferences_tmp is None:
            # inconsistent assignment, reverse inferences and return None
            for infer in inferences:
                assignment.varDomains[infer[0]].add(infer[1])
            return None
        if len(inferences_tmp) > 0:
            # if it has been revised, if not, do not do anything
            # update inferences list
            inferences = inferences.union(inferences_tmp)
            for cont in (c for c in csp.binaryConstraints if c.affects(vari)):
                vark = cont.otherVariable(vari)
                if assignment.isAssigned(vark) == False:
                    queue.append((vark, vari, constraint))

    return inferences
            


# = = = = = = = QUESTION 6  = = = = = = = #


def AC3(assignment, csp):
    """
    AC3 algorithm for constraint propagation.
    Used as a pre-processing step to reduce the problem
    before running recursive backtracking.

    Args:
        assignment (Assignment): the partial assignment to expand
        csp (ConstraintSatisfactionProblem): the problem description
    Returns:
        Assignment
        the updated assignment after inferences are made or None if an inconsistent assignment
    """
    inferences = set([])

    # TODO: Question 6
    #  Hint: implement revise first and use it as a helper function"""
    queue = Deque()
    # initialize queue
    for var in csp.varDomains:
        # consider all the variables in the variable domains
        for constraint in (c for c in csp.binaryConstraints if c.affects(var)):
            other_var = constraint.otherVariable(var)
            # if assignment.isAssigned(other_var) == False:
            queue.append((other_var, var, constraint))

    while len(queue) > 0:
        vari, varj, constraint = queue.pop()
        inferences_tmp = revise(assignment, csp, vari, varj, constraint)
        if inferences_tmp is None:
            # inconsistent assignment, reverse inferences and return None
            for infer in inferences:
                assignment.varDomains[infer[0]].add(infer[1])
            return None
        if len(inferences_tmp) > 0:
            # if it has been revised
            inferences = inferences.union(inferences_tmp)
            for cont in (c for c in csp.binaryConstraints if c.affects(vari)):
                vark = cont.otherVariable(vari)
                if not assignment.isAssigned(vark):
                    queue.append((vark, vari, constraint))
    return assignment



def solve(csp, orderValuesMethod=leastConstrainingValuesHeuristic,
          selectVariableMethod=minimumRemainingValuesHeuristic,
          inferenceMethod=forwardChecking, useAC3=True):
    """
    Solves a binary constraint satisfaction problem.

    Args:
        csp (ConstraintSatisfactionProblem): a CSP to be solved
        orderValuesMethod (function): a function to decide the next value to try
        selectVariableMethod (function): a function to decide which variable to assign next
        inferenceMethod (function): a function to specify what type of inferences to use
        useAC3 (boolean): specifies whether to use the AC3 pre-processing step or not
    Returns:
        dictionary<string, value>
        A map from variables to their assigned values. None if no solution exists.
    """
    assignment = Assignment(csp)

    assignment = eliminateUnaryConstraints(assignment, csp)
    if assignment is None:
        return assignment

    if useAC3:
        assignment = AC3(assignment, csp)
        if assignment is None:
            return assignment

    assignment = recursiveBacktracking(assignment, csp, orderValuesMethod, selectVariableMethod, inferenceMethod)
    if assignment is None:
        return assignment

    return assignment.extractSolution()
