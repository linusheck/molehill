from stormpy.storage import SparseMatrixBuilder, BitVector, StateLabeling

class MatrixGenerator:
    def __init__(self, complete_transition_matrix, global_bounds):
        self.complete_transition_matrix = complete_transition_matrix
        self.global_bounds = global_bounds
        self.decision_matrix = self._build_decision_matrix()

    def _build_decision_matrix(self):
        print("Building decision matrix")
        builder = SparseMatrixBuilder(has_custom_row_grouping=True)
        zero_state = self.complete_transition_matrix.nr_columns
        one_state = self.complete_transition_matrix.nr_columns + 1
        new_row_counter = 0
        # make iterator over quotient_choice_map
        for state in range(self.complete_transition_matrix.nr_columns):
            row_group_start = self.complete_transition_matrix.get_row_group_start(state)
            row_group_end = self.complete_transition_matrix.get_row_group_end(state)
            builder.new_row_group(new_row_counter)
            for row in range(row_group_start, row_group_end):
                for entry in self.complete_transition_matrix.get_row(row):
                    builder.add_next_value(new_row_counter, entry.column, entry.value())
                new_row_counter += 1
            builder.add_next_value(new_row_counter, zero_state, 1-self.global_bounds[state])
            builder.add_next_value(new_row_counter, one_state, self.global_bounds[state])
            new_row_counter += 1
        builder.new_row_group(new_row_counter)
        builder.add_next_value(new_row_counter, zero_state, 1)
        builder.new_row_group(new_row_counter + 1)
        builder.add_next_value(new_row_counter + 1, one_state, 1)
        print("Done decision matrix")
        return builder.build()

    def build_matrix2(self, sub_mdp, included_choices):
        transition_matrix = sub_mdp.model.transition_matrix
        builder = SparseMatrixBuilder(has_custom_row_grouping=True)
        zero_state = sub_mdp.model.nr_states
        one_state = sub_mdp.model.nr_states + 1
        new_row_counter = 0
        for state in range(sub_mdp.model.nr_states):
            row_group_start = transition_matrix.get_row_group_start(state)
            row_group_end = transition_matrix.get_row_group_end(state)
            builder.new_row_group(new_row_counter)
            added_something = False
            for row in range(row_group_start, row_group_end):
                if sub_mdp.quotient_choice_map[row] in included_choices:
                    added_something = True
                    for entry in transition_matrix.get_row(row):
                        builder.add_next_value(new_row_counter, entry.column, entry.value())
                    new_row_counter += 1
            if not added_something:
                builder.add_next_value(new_row_counter, zero_state, 1-self.global_bounds[sub_mdp.quotient_state_map[state]])
                builder.add_next_value(new_row_counter, one_state, self.global_bounds[sub_mdp.quotient_state_map[state]])
                new_row_counter += 1
        builder.new_row_group(new_row_counter)
        builder.add_next_value(new_row_counter, zero_state, 1)
        builder.new_row_group(new_row_counter + 1)
        builder.add_next_value(new_row_counter + 1, one_state, 1)
        
        new_matrix = builder.build()
        return new_matrix


    def build_matrix(self, sub_mdp, included_choices):
        include_row_bit_vector = BitVector(self.decision_matrix.nr_rows, False)
        include_column_bit_vector = BitVector(self.decision_matrix.nr_columns, False)

        next_quotient_choice_i = 0
        state_in_quotient_i = 0
        for state_in_decision_matrix in range(self.decision_matrix.nr_columns - 2):
            state_in_quotient = sub_mdp.quotient_state_map[state_in_quotient_i] if state_in_quotient_i < len(sub_mdp.quotient_state_map) else None
            row_group_start = self.decision_matrix.get_row_group_start(state_in_decision_matrix)
            row_group_end = self.decision_matrix.get_row_group_end(state_in_decision_matrix)
            # is there no state in the quotient that corresponds to this state?
            #print("state in decision matrix", state_in_decision_matrix, "state in quotient", state_in_quotient)
            if state_in_quotient != state_in_decision_matrix:
                continue
            # there are some choices here that we should include
            # next_quotient_choice already points to the first one of those

            quotient_row_group_end = sub_mdp.model.transition_matrix.get_row_group_end(state_in_quotient_i)

            complete_row_group_start = self.complete_transition_matrix.get_row_group_start(state_in_quotient)

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
            include_column_bit_vector.set(self.decision_matrix.nr_columns - i, True)
            include_row_bit_vector.set(self.decision_matrix.nr_rows - i, True)
        
        submatrix = self.decision_matrix.submatrix(include_row_bit_vector, include_column_bit_vector, False, False)
        return submatrix

    def build_state_labeling(self, sub_mdp, one_states):
        state_labeling = StateLabeling(sub_mdp.model.nr_states + 2)
        state_labeling.add_label("counterexample_target")
        for state in range(sub_mdp.model.nr_states):
            for label in sub_mdp.model.labeling.get_labels_of_state(state):
                if not state_labeling.contains_label(label):
                    state_labeling.add_label(label)
                state_labeling.add_label_to_state(label, state)
            if state in one_states:
                state_labeling.add_label_to_state("counterexample_target", state)
        state_labeling.add_label_to_state("counterexample_target", sub_mdp.model.nr_states + 1)
        return state_labeling
