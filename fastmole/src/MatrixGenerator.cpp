
#include "MatrixGenerator.h"
#include <storm/models/sparse/StateLabeling.h>

template <typename ValueType>
MatrixGenerator<ValueType>::MatrixGenerator(const storm::storage::SparseMatrix<ValueType>& completeTransitionMatrix, const std::vector<ValueType>& globalBounds)
    : completeTransitionMatrix(completeTransitionMatrix), globalBounds(globalBounds) {
    decisionMatrix = buildDecisionMatrix();
}
template <typename ValueType>
storm::storage::SparseMatrix<ValueType> MatrixGenerator<ValueType>::buildDecisionMatrix() {
    storm::storage::SparseMatrixBuilder<ValueType> builder(0, 0, 0, true, true);
    std::cout << "completeTransitionMatrix.getRowCount(): " << completeTransitionMatrix.getRowCount() << std::endl;
    std::cout << "completeTransitionMatrix.getColumnCount(): " << completeTransitionMatrix.getColumnCount() << std::endl;
    auto zeroState = completeTransitionMatrix.getColumnCount();
    auto oneState = completeTransitionMatrix.getColumnCount() + 1;
    std::size_t newRowCounter = 0;

    for (std::size_t state = 0; state < completeTransitionMatrix.getColumnCount(); ++state) {
        auto rowGroupStart = completeTransitionMatrix.getRowGroupIndices()[state];
        auto rowGroupEnd = completeTransitionMatrix.getRowGroupIndices()[state + 1];
        builder.newRowGroup(newRowCounter);
        for (std::size_t row = rowGroupStart; row < rowGroupEnd; ++row) {
            for (const auto& entry : completeTransitionMatrix.getRow(row)) {
                builder.addNextValue(newRowCounter, entry.getColumn(), entry.getValue());
            }
            ++newRowCounter;
        }
        builder.addNextValue(newRowCounter, zeroState, storm::utility::one<ValueType>() - globalBounds[state]);
        builder.addNextValue(newRowCounter, oneState, globalBounds[state]);
        ++newRowCounter;
    }
    builder.newRowGroup(newRowCounter);
    builder.addNextValue(newRowCounter, zeroState, storm::utility::one<ValueType>());
    builder.newRowGroup(newRowCounter + 1);
    builder.addNextValue(newRowCounter + 1, oneState, storm::utility::one<ValueType>());

    return builder.build();
}
template <typename ValueType>
storm::storage::SparseMatrix<ValueType> MatrixGenerator<ValueType>::buildMatrix(
    const std::vector<uint64_t> quotientStateMap,
    const storm::storage::SparseMatrix<ValueType>& subMdpMatrix,
    const std::set<uint64_t> includedChoices
) {
    storm::storage::BitVector includeRowBitVector(decisionMatrix.getRowCount(), false);
    storm::storage::BitVector includeColumnBitVector(decisionMatrix.getColumnCount(), false);

    std::size_t nextQuotientChoiceIndex = 0;
    std::size_t stateInQuotientIndex = 0;
    for (std::size_t stateInDecisionMatrix = 0; stateInDecisionMatrix < decisionMatrix.getColumnCount() - 2; ++stateInDecisionMatrix) {
        auto stateInQuotient = (stateInQuotientIndex < quotientStateMap.size()) ? quotientStateMap.at(stateInQuotientIndex) : std::numeric_limits<uint64_t>::max();
        auto rowGroupStart = decisionMatrix.getRowGroupIndices()[stateInDecisionMatrix];
        auto rowGroupEnd = decisionMatrix.getRowGroupIndices()[stateInDecisionMatrix + 1];

        if (stateInQuotient != stateInDecisionMatrix) {
            continue;
        }

        auto quotientRowGroupEnd = subMdpMatrix.getRowGroupIndices()[stateInQuotientIndex + 1];
        auto completeRowGroupStart = completeTransitionMatrix.getRowGroupIndices()[stateInQuotient];

        while (nextQuotientChoiceIndex < quotientStateMap.size() && nextQuotientChoiceIndex < quotientRowGroupEnd) {
            auto choice = quotientStateMap.at(nextQuotientChoiceIndex);
            if (std::find(includedChoices.begin(), includedChoices.end(), choice) != includedChoices.end()) {
                includeRowBitVector.set(rowGroupStart + (choice - completeRowGroupStart), true);
            } else {
                includeRowBitVector.set(rowGroupEnd - 1, true);
            }
            includeColumnBitVector.set(stateInDecisionMatrix, true);
            ++nextQuotientChoiceIndex;
        }
        ++stateInQuotientIndex;
    }

    for (std::size_t i = 1; i <= 2; ++i) {
        includeColumnBitVector.set(decisionMatrix.getColumnCount() - i, true);
        includeRowBitVector.set(decisionMatrix.getRowCount() - i, true);
    }

    auto submatrix = decisionMatrix.getSubmatrix(false, includeRowBitVector, includeColumnBitVector, false);
    return submatrix;
}

    // def build_state_labeling(self, sub_mdp, one_states):
    //     state_labeling = StateLabeling(sub_mdp.model.nr_states + 2)
    //     state_labeling.add_label("counterexample_target")
    //     for state in range(sub_mdp.model.nr_states):
    //         for label in sub_mdp.model.labeling.get_labels_of_state(state):
    //             if not state_labeling.contains_label(label):
    //                 state_labeling.add_label(label)
    //             state_labeling.add_label_to_state(label, state)
    //         if state in one_states:
    //             state_labeling.add_label_to_state("counterexample_target", state)
    //     state_labeling.add_label_to_state("counterexample_target", sub_mdp.model.nr_states + 1)
    //     return state_labeling
template <typename ValueType>
storm::models::sparse::StateLabeling MatrixGenerator<ValueType>::buildStateLabeling(
    const storm::storage::SparseMatrix<ValueType>& subMdpMatrix,
    const storm::models::sparse::StateLabeling& subMdpLabeling,
    const std::vector<std::size_t>& oneStates
) {
    std::cout << "subMdpMatrix.getColumnCount(): " << subMdpMatrix.getColumnCount() << std::endl;
    storm::models::sparse::StateLabeling stateLabeling(subMdpMatrix.getColumnCount() + 2);
    stateLabeling.addLabel("counterexample_target");

    for (std::size_t state = 0; state < subMdpMatrix.getColumnCount(); ++state) {
        for (const auto& label : subMdpLabeling.getLabelsOfState(state)) {
            if (!stateLabeling.containsLabel(label)) {
                stateLabeling.addLabel(label);
            }
            stateLabeling.addLabelToState(label, state);
        }
        if (std::find(oneStates.begin(), oneStates.end(), state) != oneStates.end()) {
            stateLabeling.addLabelToState("counterexample_target", state);
        }
    }
    stateLabeling.addLabelToState("counterexample_target", subMdpMatrix.getColumnCount() + 1);

    return stateLabeling;
}

template class MatrixGenerator<double>;
template class MatrixGenerator<storm::RationalFunction>;
