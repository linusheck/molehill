"""Test search space"""

import pytest
import z3
from molehill import run
from molehill.constraints import DecisionTree
from argparse import Namespace
import time

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

@pytest.mark.parametrize("tree", [1, 3, 5, 7])
def test_tree_enumeration(tree):
    constraint = DecisionTree(robust=False)
    constraint.set_args(Namespace(forall="sketch_hole", random=False, nodes=tree, picture_path=None))
    variables = [z3.BitVec(f"A([x={x}&y={y}])", 2) for x in range(3) for y in range(3)]
    f = z3.Function("valid", *[x.sort() for x in variables], z3.BoolSort())
    constraints = constraint.build_constraint(f, variables, lambda x: True)

    s = z3.Solver()
    s.add(constraints)

    all_models, time_spent = all_smt(s)

    # print(len(all_models))
    # print(all_models)
    # for i in range(len(all_models)):
    #     constraint.args.picture_path = f"resources/test/alltrue/decision_tree_{tree}_{i}.png"
    #     constraint.show_result(all_models[i], s)
    
    # Check if the number of models is equal to the expected number
    expected_number = {1: 3, 3: 54, 5: 1944, 7: 174960}
    assert len(all_models) == expected_number[tree], f"Expected {expected_number[tree]} models, but got {len(all_models)}"
