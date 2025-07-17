"""Molehill is a Markov chain searcher."""

import paynt.quotient
import paynt.quotient.mdp_family
import paynt.quotient.pomdp
import z3
import paynt.parser.sketch
import math
import payntbind.synthesis
import json

from molehill.mole import Mole


def run(
    project_path,
    considered_counterexamples,
    constraint,
    exact=False,
    search_space_test=False,
    fsc_memory_size=1,
    print_reasons=False,
    image=False,
    plot_function_args=False,
    verbose=False,
    pure_smt=False,
):
    sketch_path = f"{project_path}/sketch.templ"
    properties_path = f"{project_path}/sketch.props"
    paynt.quotient.pomdp.PomdpQuotient.initial_memory_size = fsc_memory_size
    paynt.quotient.mdp_family.MdpFamilyQuotient.initial_memory_size = fsc_memory_size
    # TODO Exact mode: why does this not give me an exact MDP
    quotient = paynt.parser.sketch.Sketch.load_sketch(
        sketch_path, properties_path, use_exact=exact
    )

    print(quotient.family)
    # print all python properties of quotient
    family = quotient.family

    if isinstance(
        quotient, paynt.quotient.pomdp_family.PomdpFamilyQuotient
    ) or isinstance(quotient, paynt.quotient.mdp_family.MdpFamilyQuotient):
        quotient.family.hole_to_name = [
            "sketch_hole_" + x for x in quotient.family.hole_to_name
        ]  # feel free to change the prefix, this should just make it easier to creat exists forall queries

        choice_to_hole_options = quotient.coloring.getChoiceToAssignment()

        if isinstance(quotient, paynt.quotient.pomdp_family.PomdpFamilyQuotient):
            obs_to_hole = []
            for obs in range(quotient.num_observations):
                obs_mem_holes = []
                for mem in range(fsc_memory_size):
                    if (
                        len(quotient.observation_to_actions[obs]) > 1
                    ):  # if there's only one choice in an observation there's no point in adding a hole
                        # here would come potential memory size
                        option_labels = [
                            quotient.action_labels[i]
                            for i in quotient.observation_to_actions[obs]
                        ]
                        hole_name = f"(obs_{obs},{mem})"  # getting the observation expressions is a bit more complicated, and I don't think it's important for now
                        obs_mem_holes.append(quotient.family.num_holes)
                        quotient.family.add_hole(hole_name, option_labels)
                obs_to_hole.append(obs_mem_holes)

            nci = quotient.quotient_mdp.nondeterministic_choice_indices.copy()

            if fsc_memory_size > 1:
                state_memories = list(quotient.memory_unfolder.state_memory)
            else:
                state_memories = [0 for _ in range(quotient.quotient_mdp.nr_states)]
            for state in range(quotient.quotient_mdp.nr_states):
                obs = quotient.obs_evaluator.state_to_obs_class[state]
                state_mem = state_memories[state]
                obs_holes = obs_to_hole[obs]
                if state_mem < len(obs_holes):
                    obs_hole = obs_holes[state_mem]
                    for choice in range(nci[state], nci[state + 1]):
                        action_hole_index = quotient.observation_to_actions[obs].index(
                            quotient.choice_to_action[choice]
                        )
                        choice_to_hole_options[choice].append(
                            (obs_hole, action_hole_index)
                        )

            quotient.coloring = payntbind.synthesis.Coloring(
                family.family,
                quotient.quotient_mdp.nondeterministic_choice_indices,
                choice_to_hole_options,
            )
        else:  # meaning it is a MdpFamilyQuotient

            def _get_state_valuations(model):
                """Identify variable names and extract state valuation in the same order."""
                assert model.has_state_valuations(), "model has no state valuations"
                # get name
                sv = model.state_valuations
                variable_name = None
                state_valuations = []
                for state in range(model.nr_states):
                    valuation = json.loads(str(sv.get_json(state)))
                    if variable_name is None:
                        variable_name = list(valuation.keys())
                    valuation = [valuation[var_name] for var_name in variable_name]
                    state_valuations.append(valuation)
                return variable_name, state_valuations

            if fsc_memory_size == 1:
                var_names, state_valuations = _get_state_valuations(quotient.quotient_mdp)
            nci = quotient.quotient_mdp.nondeterministic_choice_indices.copy()
            for state in range(quotient.quotient_mdp.nr_states):
                if (
                    len(quotient.state_to_actions[state]) > 1
                ):  # again if there's only one action in a state there's no point in adding a hole
                    option_labels = [
                        quotient.action_labels[i]
                        for i in quotient.state_to_actions[state]
                    ]
                    if fsc_memory_size == 1:
                        vals_here = "&".join(
                            [
                                f"{var_name}={int(state_valuations[state][i])}"
                                for i, var_name in enumerate(var_names)
                                if not var_name.startswith("_loc_prism2jani")
                            ]
                        )
                        hole_name = f"A([{vals_here}])"
                    else:
                        hole_name = f"A(S{state//2},M{state%2})"
                    hole_index = quotient.family.num_holes
                    quotient.family.add_hole(hole_name, option_labels)
                    for choice in range(nci[state], nci[state + 1]):
                        action_hole_index = quotient.state_to_actions[state].index(
                            quotient.choice_to_action[choice]
                        )
                        choice_to_hole_options[choice].append(
                            (hole_index, action_hole_index)
                        )

            quotient.coloring = payntbind.synthesis.Coloring(
                family.family,
                quotient.quotient_mdp.nondeterministic_choice_indices,
                choice_to_hole_options,
            )

        family = quotient.family

    if verbose:
        z3.set_param("smt.mbqi", True)
        z3.set_param("smt.mbqi.trace", True)
        z3.set_param("trace", True)
        z3.set_param("trace_file_name", "mbqi.log")

        # set verbose to 20
        z3.set_param("verbose", 20)

    s = z3.Solver()

    constraint.solver_settings(s)

    bit_nums = set()

    num_bits = (
        max(
            [
                math.ceil(math.log2(len(family.hole_options(hole)) + 1))
                for hole in range(family.num_holes)
            ]
        )
        + 1
    )

    variables = []

    for hole in range(family.num_holes):
        name = family.hole_name(hole)
        bit_nums.add(num_bits)
        var = z3.BitVec(name, num_bits)
        variables.append(var)

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

    # Create the valid(...) function
    f = z3.PropagateFunction("valid", *[x.sort() for x in variables], z3.BoolSort())

    s.add(
        constraint.build_constraint(
            f, variables, variables_in_ranges, family=family, quotient=quotient
        )
    )

    if pure_smt:
        from molehill.pure_smt import get_constraints
        constraints = get_constraints(
            variables,
            variables_in_ranges,
            quotient,
            f,
        )
        s.add(constraints)
        p = None

    else:
        p = Mole(
            s,
            variables,
            quotient,
            exact=exact,
            draw_image=(image or search_space_test),
            considered_counterexamples=considered_counterexamples,
        )

    model = None
    if s.check() == z3.sat:
        print("sat")
        model = s.model()
        new_family = quotient.family.copy()
        new_family.add_parent_info(quotient.family)
        for hole in range(new_family.num_holes):
            var = variables[hole]
            # if var has as_long attribute
            if hasattr(model.eval(var), "as_long"):
                new_family.hole_set_options(hole, [model.eval(var).as_long()])
        # re-check DTMC
        quotient.build(new_family)
        mdp = new_family.mdp
        prop = quotient.specification.all_properties()[0]
        result = mdp.model_check_property(prop)
        print(f"Found {new_family} with value {result}")
        constraint.show_result(model, s, family=family)
    else:
        print("unsat")
    if not pure_smt:
        print(f"Considered {p.mc_calls} models")
        if print_reasons:
            print(f"Reasons:")
            for r in p.reasons:
                print(f"  {r}")
        if sum(p.mdp_fails_and_wins) > 0:
            print(
                f"MDP checking had {p.mdp_fails_and_wins[0]} fails and {p.mdp_fails_and_wins[1]} wins ({round(p.mdp_fails_and_wins[1] / sum(p.mdp_fails_and_wins) * 100, 1)}% wins)"
            )

    if image:
        print("Drawing image")
        from molehill.plotters.curve_drawer import draw_curve

        draw_curve(num_bits, variables, s, p, model)

    if plot_function_args:
        print("Drawing function arguments")
        from molehill.plotters.function_args_drawer import draw_function_args

        draw_function_args(p)

    # return is for testing purposes
    return model, s, p
