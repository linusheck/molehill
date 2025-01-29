"""Test matrix generator"""

import pytest
from paynt.parser.sketch import Sketch
from molehill.plugin import SearchMarkovChain
from fastmole import get_possible_choices
import z3
import math
from stormpy import model_checking, check_model_sparse, parse_properties_without_context
from stormpy.storage import SparseModelComponents, SparseMdp, BitVector
from random import choice
import time

def is_approx(list_a, list_b, tol=1e-6):
    return all(abs(a - b) < tol for a, b in zip(list_a, list_b))


def is_smaller(list_a, list_b, tol=1e-6):
    return all(a < b + tol for a, b in zip(list_a, list_b))

def pad_vector_to_size(vector, size):
    return vector + [0.0] * (size - len(vector))

@pytest.mark.parametrize("project_path", ["resources/grid", "resources/safety", "resources/liveness"])
def test_matrix_generator(project_path):
    sketch_path = f"{project_path}/sketch.templ"
    properties_path = f"{project_path}/sketch.props"
    quotient = Sketch.load_sketch(sketch_path, properties_path)
    # print all python properties of quotient
    family = quotient.family

    s = z3.Solver()

    variables = []
    # create variables
    num_bits = max([math.ceil(math.log2(max(family.hole_options(hole)) + 1)) for hole in range(family.num_holes)]) + 1
    for hole in range(family.num_holes):
        name = family.hole_name(hole)
        options = family.hole_options(hole)
        var = z3.BitVec(name, num_bits)
        variables.append(var)
        s.add(z3.And(var >= z3.BitVecVal(min(options), num_bits), var <= z3.BitVecVal(max(options), num_bits)))

    new_family = family

    choice_to_assignment = quotient.coloring.getChoiceToAssignment()

    plugin = SearchMarkovChain(s, quotient)
    quotient_mdp = quotient.family.mdp.model

    # time to build the MDP
    fastmole_time = 0.0
    paynt_time = 0.0

    for hole in range(family.num_holes + 1):
        prop = quotient.specification.all_properties()[0]

        compatible_choices_holes = BitVector(quotient_mdp.transition_matrix.nr_rows, False)
        compatible_choices_mdp = BitVector(quotient_mdp.transition_matrix.nr_rows, False)
        for choice, hole_assignments in enumerate(choice_to_assignment):
            possible = True # this choice is possible (it might occur in the MDP)
            certain = True # this choice is certain (it is the only option)
            for hole, assignment in hole_assignments:
                hole_options = new_family.hole_options(hole)
                if assignment not in hole_options:
                    possible = False
                    certain = False
                    break
                if len(hole_options) > 1:
                    certain = False
            compatible_choices_holes[choice] = certain
            compatible_choices_mdp[choice] = possible

        plugin.matrix_generator.build_submodel(compatible_choices_holes)
        mdp_holes = plugin.matrix_generator.get_current_mdp()
        holes_bitvec = plugin.matrix_generator.get_current_reachable_states()
        ex_time = time.time()
        plugin.matrix_generator.build_submodel(compatible_choices_mdp)
        fastmole_time += time.time() - ex_time
        mdp_nondet = plugin.matrix_generator.get_current_mdp()
        nondet_bitvec = plugin.matrix_generator.get_current_reachable_states()

        new_property = parse_properties_without_context(str(prop.formula).split()[0] + " [ F \"counterexample_target\" ]")[0]

        ex_time = time.time()
        quotient.build(new_family)
        paynt_time += time.time() - ex_time
        result_paynt = new_family.mdp.model_check_property(prop)
        result_storm_holes = check_model_sparse(mdp_holes, new_property)
        result_storm_nondet = check_model_sparse(mdp_nondet, new_property)

        result_storm_holes_pad = [1.0] * quotient_mdp.transition_matrix.nr_rows
        for i, state_in_holes_result in enumerate(holes_bitvec):
            result_storm_holes_pad[state_in_holes_result] = result_storm_holes.get_values()[i]

        result_storm_nondet_pad = [0.0] * quotient_mdp.transition_matrix.nr_rows
        for i, state_in_nondet_result in enumerate(nondet_bitvec):
            result_storm_nondet_pad[state_in_nondet_result] = result_storm_nondet.get_values()[i]

        assert is_smaller(result_storm_nondet_pad, result_storm_holes_pad, 1e-4)
        assert is_approx(result_paynt.result.get_values(), result_storm_nondet.get_values(), 1e-4)

        if hole < family.num_holes:
            new_family.hole_set_options(hole, [new_family.hole_options(hole)[-1]])
            new_family.add_parent_info(family)

    assert fastmole_time < paynt_time
