"""Test matrix generator"""

import pytest
from paynt.parser.sketch import Sketch
from mdpcegis.plugin import SearchMarkovChain
import z3
import math
from stormpy import model_checking, check_model_sparse, parse_properties_without_context
from stormpy.storage import SparseModelComponents, SparseMdp

@pytest.mark.parametrize("project_path", ["resources/"])
def test_matrix_generator(project_path):
    sketch_path = f"{project_path}/sketch.templ"
    properties_path = f"{project_path}/sketch.props"
    quotient = Sketch.load_sketch(sketch_path, properties_path)
    # print all python properties of quotient
    family = quotient.family

    quotient.build(family)

    s = z3.Solver()

    variables = []
    # create variables
    num_bits = max([math.ceil(math.log2(max(family.hole_options(hole)) + 1)) for hole in range(family.num_holes)]) + 1
    for hole in range(family.num_holes):
        name = family.hole_name(hole)
        options = family.hole_options(hole)
        var = z3.BitVec(name, num_bits)
        variables.append(var)
        # TODO hole options of full family should be a sorted vector of indices that is continous
        s.add(z3.And(var >= z3.BitVecVal(min(options), num_bits), var <= z3.BitVecVal(max(options), num_bits)))

    plugin = SearchMarkovChain(s, quotient)

    sub_mdp = quotient.family.mdp

    prop = quotient.specification.all_properties()[0]

    target_state = model_checking(sub_mdp.model, prop.formula.subformula.subformula).get_truth_values()
    one_states = [state for state in range(sub_mdp.model.nr_states) if target_state.get(state)]

    choice_to_assignment = quotient.coloring.getChoiceToAssignment()
    state_to_holes = quotient.coloring.getStateToHoles()

    matrix_generator = plugin.matrix_generator
    state_to_holes_bv = quotient.coloring.getStateToHoles().copy()
    state_to_holes = []
    all_holes = set()
    for _state, holes_bv in enumerate(state_to_holes_bv):
        holes = set([hole for hole in holes_bv])
        all_holes.update(holes)
        state_to_holes.append(holes)
    print(all_holes)
    matrix = matrix_generator.build_matrix(sub_mdp, all_holes)
    labeling = matrix_generator.build_state_labeling(sub_mdp, one_states)

    model_components = SparseModelComponents()
    model_components.transition_matrix = matrix
    model_components.state_labeling = labeling

    new_property = parse_properties_without_context(str(prop.formula).split()[0] + " [ F \"counterexample_target\" ]")[0]

    new_mdp = SparseMdp(model_components)

    open("sub_mdp.dot", "w").write(sub_mdp.model.to_dot())
    open("new_mdp.dot", "w").write(new_mdp.to_dot())

    result_paynt = quotient.family.mdp.model_check_property(prop)
    result_storm = check_model_sparse(new_mdp, new_property)

    assert result_paynt.result.get_values() == result_storm.get_values()

    assert False, new_mdp
