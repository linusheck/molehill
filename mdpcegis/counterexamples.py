"""Compute counterexamples."""

from stormpy import check_model_sparse, model_checking, parse_properties_without_context
from stormpy import ExplicitModelCheckerHintDouble
import stormpy.storage
import stormpy.core
from stormpy import model_checking
from stormpy.storage import SparseMatrixBuilder
import z3

def build_decision_matrix(transition_matrix, global_bounds):
    print("Building decision matrix")
    builder = SparseMatrixBuilder(has_custom_row_grouping=True)
    zero_state = transition_matrix.nr_columns
    one_state = transition_matrix.nr_columns + 1
    new_row_counter = 0
    # make iterator over quotient_choice_map
    for state in range(transition_matrix.nr_columns):
        row_group_start = transition_matrix.get_row_group_start(state)
        row_group_end = transition_matrix.get_row_group_end(state)
        builder.new_row_group(new_row_counter)
        for row in range(row_group_start, row_group_end):
            for entry in transition_matrix.get_row(row):
                builder.add_next_value(new_row_counter, entry.column, entry.value())
            new_row_counter += 1
        builder.add_next_value(new_row_counter, zero_state, global_bounds.at(state))
        builder.add_next_value(new_row_counter, one_state, 1-global_bounds.at(state))
        new_row_counter += 1
    builder.new_row_group(new_row_counter)
    builder.add_next_value(new_row_counter, zero_state, 1)
    builder.new_row_group(new_row_counter + 1)
    builder.add_next_value(new_row_counter + 1, one_state, 1)
    print("Done decision matrix")
    return builder.build()

def _build_matrix(sub_mdp, complete_transition_matrix, transition_matrix, decision_matrix, one_states, included_choices):
    include_row_bit_vector = stormpy.storage.BitVector(decision_matrix.nr_rows, False)
    include_column_bit_vector = stormpy.storage.BitVector(decision_matrix.nr_columns, False)

    next_quotient_choice_i = 0
    state_in_quotient_i = 0
    for state_in_decision_matrix in range(decision_matrix.nr_columns - 2):
        state_in_quotient = sub_mdp.quotient_state_map[state_in_quotient_i] if state_in_quotient_i < len(sub_mdp.quotient_state_map) else None
        row_group_start = decision_matrix.get_row_group_start(state_in_decision_matrix)
        row_group_end = decision_matrix.get_row_group_end(state_in_decision_matrix)
        # is there no state in the quotient that corresponds to this state?
        #print("state in decision matrix", state_in_decision_matrix, "state in quotient", state_in_quotient)
        if state_in_quotient != state_in_decision_matrix:
            #print("include hole", row_group_end - 1)
            continue
        # there are some choices here that we should include
        # next_quotient_choice already points to the first one of those

        quotient_row_group_end = transition_matrix.get_row_group_end(state_in_quotient_i)

        complete_row_group_start = complete_transition_matrix.get_row_group_start(state_in_quotient)

        while next_quotient_choice_i < len(sub_mdp.quotient_choice_map) and next_quotient_choice_i < quotient_row_group_end:
            choice = sub_mdp.quotient_choice_map[next_quotient_choice_i]
            if choice in included_choices:
                # print("include choice", next_quotient_choice_i, "at", state_in_decision_matrix, "which is", choice)
                include_row_bit_vector.set(row_group_start + (choice - complete_row_group_start), True)
            else:
                # there is some hole here, so map that to hole state
                include_row_bit_vector.set(row_group_end - 1, True)
            include_column_bit_vector.set(state_in_decision_matrix, True)
            next_quotient_choice_i += 1
        state_in_quotient_i += 1

    # also include the last two columns, which are the zero and one states
    for i in range(1, 3):
        include_column_bit_vector.set(decision_matrix.nr_columns - i, True)
        include_row_bit_vector.set(decision_matrix.nr_rows - i, True)

    submatrix = decision_matrix.submatrix(include_row_bit_vector, include_column_bit_vector, False, False)

    state_labeling = stormpy.storage.StateLabeling(sub_mdp.model.nr_states + 2)
    state_labeling.add_label("counterexample_target")
    for state in range(sub_mdp.model.nr_states):
        for label in sub_mdp.model.labeling.get_labels_of_state(state):
            if not state_labeling.contains_label(label):
                state_labeling.add_label(label)
            state_labeling.add_label_to_state(label, state)
        if state in one_states:
            state_labeling.add_label_to_state("counterexample_target", state)
    state_labeling.add_label_to_state("counterexample_target", submatrix.nr_columns - 1)

    model_components = stormpy.storage.SparseModelComponents()
    model_components.transition_matrix = submatrix
    model_components.state_labeling = state_labeling

    return model_components

def compute_counterexample(sub_mdp, mc_result, variables, partial_model, state_to_holes, choice_to_assignment, prop, decision_matrix, complete_transition_matrix, model_counter):
    # pathlib.Path(f"dots/mdp_{partial_model}.dot").write_text(sub_mdp.model.to_dot(), encoding="utf-8")
    transition_matrix = sub_mdp.model.transition_matrix

    included_holes = [hole for hole in range(len(variables)) if variables[hole] not in partial_model]
    included_choices = set([choice for choice in range(len(choice_to_assignment)) if all([hole in included_holes for hole, _ in choice_to_assignment[choice]])])
    included_fixed_holes = []

    all_schedulers_violate = False

    target_state = model_checking(sub_mdp.model, prop.formula.subformula.subformula).get_truth_values()
    one_states = [state for state in range(sub_mdp.model.nr_states) if target_state.get(state)]

    hint = None

    while not all_schedulers_violate:
        model_components = _build_matrix(sub_mdp, complete_transition_matrix, transition_matrix, decision_matrix, one_states, included_choices)

        # TODO hack (i hate properties)
        new_property = parse_properties_without_context(str(prop.formula).split()[0] + f" [ F \"counterexample_target\" ]")[0]

        # model check filtered matrix
        new_mdp = stormpy.storage.SparseMdp(model_components)

        # for state in range(sub_mdp.model.nr_states):
        #     # also #print variable valuations
        #     #print(sub_mdp.quotient_choice_map[state], result2.at(state))

        result = check_model_sparse(new_mdp, new_property, extract_scheduler=True, hint=hint)
        #print(result.get_values())
        hint = ExplicitModelCheckerHintDouble()
        hint.set_result_hint(result.get_values())
        hint.set_scheduler_hint(result.scheduler)
        all_schedulers_violate = not prop.satisfies_threshold(result.at(sub_mdp.model.initial_states[0]))

        # pathlib.Path(f"dots/counterexample_{partial_model}_{len(included_holes)}.dot").write_text(new_mdp.to_dot(), encoding="utf-8")

        if not all_schedulers_violate:
            condition_before_candidate = z3.And(*[variables[hole] == partial_model[variables[hole]] for hole in included_fixed_holes])
            assignment_candidates = [None if hole in included_holes else variables[hole] == partial_model[variables[hole]] for hole in range(len(variables))]

            model_counts = []
            for candidate in assignment_candidates:
                if candidate is None:
                    model_counts.append(0)
                else:
                    # model_counts.append(model_counter.count_models(max_models=64, condition=candidate))
                    model_counts.append(int(model_counter.is_sat(z3.And(candidate, condition_before_candidate))))

            # choose a hole to include now
            hole_scores = [0.0] * len(variables)
            for state, quotient_state in enumerate(sub_mdp.quotient_state_map):
                for hole in state_to_holes[quotient_state]:
                    if not hole in included_holes:
                        hole_scores[hole] += mc_result.at(state)

            add_new_hole = True

            print(model_counts)
            print(hole_scores)

            # score = [(int(hole_scores[hole] > 0), model_counts[hole], hole_scores[hole]) for hole in range(len(variables))]
            score = [(int(hole_scores[hole] > 0), hole_scores[hole], hole_scores[hole]) for hole in range(len(variables))]
            # print(score)

            while add_new_hole:
                # max_hole = max(range(len(hole_scores)), key=lambda hole: hole_scores[hole])
                max_hole = sorted(set(range(len(variables))) - set(included_holes), key=lambda hole: score[hole])[-1]
                print("=>", max_hole)
                if score[max_hole][1] * score[max_hole][2] <= 0.0:
                    return None
                included_holes.append(max_hole)
                included_fixed_holes.append(max_hole)
                hole_scores[max_hole] = -1
                if len(included_holes) == len(variables):
                    return included_fixed_holes
                # Check if we have enabled a new action
                for choice, assignment in enumerate(choice_to_assignment):
                    holes = [x[0] for x in assignment]
                    if max_hole in holes and all([hole in included_holes for hole in holes]):
                        included_choices.add(choice)
                        add_new_hole = False
                # assert included_choices == set([choice for choice in range(len(choice_to_assignment)) if all([hole in included_holes for hole, _ in choice_to_assignment[choice]])])
        else:
            return included_fixed_holes
    raise RuntimeError("No counterexample found")

