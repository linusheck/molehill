"""Test search space"""

import pytest
import z3
from molehill import run
from molehill.constraints import DecisionTree
from argparse import Namespace
import time
from paynt.family.family import Family

def block_model(s):
    m = s.model()
    s.add(z3.Or([ f() != m[f] for f in m.decls() if f.arity() == 0]))           

def all_smt(s):
    all_models = []
    time_spent_in_check = 0
    last_time = time.time()
    while z3.sat == s.check():
        current_time = time.time()
        time_spent_in_check += current_time - last_time
        all_models.append(s.model())
        block_model(s)
        last_time = current_time
    return all_models, time_spent_in_check

@pytest.mark.parametrize("tree", [1, 3, 5])
@pytest.mark.parametrize("tree_case", [0, 1, 2])
def test_tree_enumeration(tree, tree_case):
    num_bits = 3
    constraint = DecisionTree(robust=False)
    constraint.set_args(Namespace(forall="sketch_hole", random=False, nodes=tree, picture_path=None))
    variables = [z3.BitVec(f"A([x={x}&y={y}])", num_bits) for x in range(3) for y in range(4)]
    f = z3.Function("valid", *[x.sort() for x in variables], z3.BoolSort())

    family = Family()
    if tree_case == 0:
        for var in variables:
            family.add_hole(str(var), ["left", "right", "up", "down"])
    elif tree_case == 1:
        # Give it different labels
        for var in variables[:len(variables) // 2]:
            family.add_hole(str(var), ["left", "right", "up", "down"])
        for var in variables[len(variables) // 2:]:
            family.add_hole(str(var), ["up", "down", "left"])
    elif tree_case == 2:
        # Give it more different labels
        for var in variables[:len(variables) // 2]:
            family.add_hole(str(var), ["up", "down"])
        for var in variables[len(variables) // 2:]:
            family.add_hole(str(var), ["left", "right"])

    def variables_in_ranges(variables):
        statement = []
        for hole in range(family.num_holes):
            options = family.hole_options(hole)
            # it gets guaranteed by paynt that this is actually the range
            # (these are just the indices, not the actual values in the final model :)
            assert min(options) == 0
            var = variables[hole]
            statement.append(z3.UGE(var, z3.BitVecVal(min(options), num_bits)))
            statement.append(z3.ULE(var, z3.BitVecVal(max(options), num_bits)))
        return z3.And(*statement)

    constraints = constraint.build_constraint(f, variables, variables_in_ranges, family=family)

    s = z3.Solver()
    s.add(constraints)
    print(constraints)

    all_models, time_spent = all_smt(s)

    # if not simple_tree and tree < 5:
    #     for i in range(len(all_models)):
    #         constraint.args.picture_path = f"resources/test/alltrue/decision_tree_{tree}_{i}.png"
    #         constraint.show_result(all_models[i], s, family=family)
    
    # Check if the number of models is equal to the expected number
    expected_number = None
    if tree_case == 0:
        expected_number = {1: 4, 3: 112, 5: 6272}
    elif tree_case == 1:
        expected_number = {1: 3, 3: 72, 5: 3762} # TODO Check
    elif tree_case == 2:
        expected_number = {1: 0, 3: 0, 5: 0}
    assert len(all_models) == expected_number[tree], f"Expected {expected_number[tree]} models, but got {len(all_models)}"
