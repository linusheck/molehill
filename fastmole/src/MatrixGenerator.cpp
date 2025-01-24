
#include "MatrixGenerator.h"
#include <queue>
#include <storm/storage/BitVector.h>
#include <storm/storage/sparse/ModelComponents.h>

template <typename ValueType>
MatrixGenerator<ValueType>::MatrixGenerator(const storm::models::sparse::Mdp<ValueType>& quotient, storm::storage::BitVector targetStates, const std::vector<ValueType>& globalBounds)
    : quotient(quotient), targetStates(targetStates), globalBounds(globalBounds) {
    decisionMatrix = buildDecisionMatrix();
}
template <typename ValueType>
storm::storage::SparseMatrix<ValueType> MatrixGenerator<ValueType>::buildDecisionMatrix() {
    auto const& completeTransitionMatrix = quotient.getTransitionMatrix();
    storm::storage::SparseMatrixBuilder<ValueType> builder(0, 0, 0, true, true);
    auto zeroState = completeTransitionMatrix.getColumnCount();
    auto oneState = completeTransitionMatrix.getColumnCount() + 1;
    std::size_t newRowCounter = 0;

    // The decision matrix has one additional row and column for the hole inclusion.
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

    auto const& decisionMatrix = builder.build();
    std::cout << "Decision matrix: " << decisionMatrix << std::endl;
    return decisionMatrix;
}
template <typename ValueType>
std::pair<storm::models::sparse::Mdp<ValueType>, storm::storage::BitVector> MatrixGenerator<ValueType>::buildSubModel(
    const storm::storage::BitVector includedChoices
) {
    auto const& completeTransitionMatrix = quotient.getTransitionMatrix();

    storm::storage::BitVector includeRowBitVector(decisionMatrix.getRowCount(), false);

    storm::storage::BitVector reachableStates(decisionMatrix.getColumnCount(), false);
    std::queue<uint64_t> statesToProcess;
    for (auto const& initialState : this->quotient.getInitialStates()) {
        reachableStates.set(initialState, true);
        statesToProcess.push(initialState);
    }

    // The row in the quotient (= complete transition matrix) that we are currently looking at
    while (!statesToProcess.empty()) {
        auto state = statesToProcess.front();
        statesToProcess.pop();
        if (!reachableStates.get(state)) {
            continue;
        }
        // This row group in the quotient (this is what the includedChoices BitVector is based on)
        auto rowGroupStartQuotient = completeTransitionMatrix.getRowGroupIndices()[state];
        auto rowGroupEndQuotient = completeTransitionMatrix.getRowGroupIndices()[state + 1];
        // This row group in the decision matrix (this is what our includeRowBitVector is based on)
        auto rowGroupStartDecision = decisionMatrix.getRowGroupIndices()[state];
        auto rowGroupEndDecision = decisionMatrix.getRowGroupIndices()[state + 1];

        bool someChoiceIncluded = false;
        for (uint64_t row = rowGroupStartQuotient; row < rowGroupEndQuotient; ++row) {
            if (includedChoices.get(row)) {
                someChoiceIncluded = true;
                // Include this choice
                includeRowBitVector.set(rowGroupStartDecision + (row - rowGroupStartQuotient), true);

                // Successors of this choice are reachable
                for (auto const& entry : completeTransitionMatrix.getRow(row)) {
                    if (!reachableStates.get(entry.getColumn())) {
                        reachableStates.set(entry.getColumn(), true);
                        statesToProcess.push(entry.getColumn());
                    }
                }
            }
        }
        if (!someChoiceIncluded) {
            // No choice is included, so we need to include the last row of the row group
            includeRowBitVector.set(rowGroupEndDecision - 1, true);
        }
    }

    // Always include the last two columns
    for (std::size_t i = 1; i <= 2; ++i) {
        reachableStates.set(decisionMatrix.getColumnCount() - i, true);
        includeRowBitVector.set(decisionMatrix.getRowCount() - i, true);
    }

    auto const& submatrix = decisionMatrix.getSubmatrix(false, includeRowBitVector, reachableStates, false);

    storm::models::sparse::StateLabeling stateLabeling(submatrix.getColumnCount());
    stateLabeling.addLabel("counterexample_target");

    std::cout << "Counterexample Targets: " << targetStates << std::endl;
    auto reachableStatesIterator = reachableStates.begin();
    for (std::size_t state = 0; state < submatrix.getColumnCount() - 2; ++state) {
        for (const auto& label : this->quotient.getLabelsOfState(state)) {
            if (!stateLabeling.containsLabel(label)) {
                stateLabeling.addLabel(label);
            }
            stateLabeling.addLabelToState(label, state);
        }
        if (targetStates.get(*reachableStatesIterator)) {
            stateLabeling.addLabelToState("counterexample_target", state);
        }
        reachableStatesIterator++;
    }
    stateLabeling.addLabelToState("counterexample_target", submatrix.getColumnCount() - 1);

    storm::storage::sparse::ModelComponents<ValueType> modelComponents(submatrix, stateLabeling);

    return std::make_pair(storm::models::sparse::Mdp<ValueType>(modelComponents), reachableStates);
}

template class MatrixGenerator<double>;
template class MatrixGenerator<storm::RationalFunction>;
