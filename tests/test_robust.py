"""Test robust verification"""

import paynt.synthesizer
import paynt.synthesizer.synthesizer_ar
import pytest
from molehill import run
from molehill.constraints import ExistsForallConstraint
from argparse import Namespace
import paynt
import random

# @pytest.mark.parametrize("project_path", ["resources/test/robust/obstacles-10-6-skip-easy", "resources/test/robust/mastermind-2-4-3", "resources/test/robust/rocks-4-2", "resources/test/robust/rover-100-big", "resources/test/robust/bridge-11-5-4"])
@pytest.mark.parametrize("project_path", ["resources/test/robust/rocks-4-2"])
@pytest.mark.parametrize("considered_counterexamples", ["none"])
def test_robust(project_path, considered_counterexamples):
    constraint = ExistsForallConstraint()
    constraint.set_args(Namespace(forall="sketch_hole", random=False))
    model, _solver, plugin = run(project_path, considered_counterexamples, constraint, search_space_test=False, print_reasons=False, image=False)

    assert model is not None, "solver says unsat even though we have a model"

    print(plugin.counterexamples)

    # check that all rejecting models actually reject
    # collect the z3 model as a map
    model_as_map = {str(d): model[d] for d in model} if model is not None else {}
    print(model)
    family = plugin.quotient.family.copy()
    family.add_parent_info(plugin.quotient.family)
    for hole in range(family.num_holes):
        var = plugin.model_variable_names[hole]
        if "sketch_hole" not in var:
            if var in model_as_map:
                family.hole_set_options(hole, [model_as_map[var].as_long()])

    # ask paynt to check that the family is robust
    plugin.quotient.specification = plugin.quotient.specification.negate()
    plugin.quotient.build(family)

    synthesizer = paynt.synthesizer.synthesizer_ar.SynthesizerAR(plugin.quotient)
    result = synthesizer.synthesize(family)

    # result is None means policy is robust :)
    assert result is None, f"PAYNT says that policy is not robust. Counterexample: {result}"
