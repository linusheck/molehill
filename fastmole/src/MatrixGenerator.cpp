
#include "MatrixGenerator.h"
#include <_types/_uint64_t.h>
#include <optional>
#include <queue>
#include <stdexcept>
#include <storm/storage/BitVector.h>
#include <storm/storage/sparse/ModelComponents.h>
#include <storm/utility/macros.h>
#include <vector>

template <typename ValueType>
MatrixGenerator<ValueType>::MatrixGenerator(const storm::models::sparse::Mdp<ValueType>& quotient, storm::storage::BitVector targetStates, const std::vector<ValueType>& globalBounds, const std::vector<std::vector<std::pair<int, int>>>& choiceToAssignment)
    : quotient(quotient), targetStates(targetStates), globalBounds(globalBounds), choiceToAssignment(choiceToAssignment) {
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

    return builder.build();
}

template <typename ValueType>
bool MatrixGenerator<ValueType>::isChoicePossible(
        const storm::storage::BitVector& abstractedHoles,
        const std::vector<storm::storage::BitVector>& holeOptions,
        uint64_t choice
    ) {
    if (choice >= this->choiceToAssignment.size()) {
        throw std::runtime_error("Choice index " + std::to_string(choice) + " out of bounds (size: " + std::to_string(this->choiceToAssignment.size()) + ")");
    }
    for (auto const& [hole, assignment] : this->choiceToAssignment.at(choice)) {
        if (abstractedHoles.get(hole)) {
            // This choice is abstracted
            return false;
        }
        if (hole >= holeOptions.size()) {
            throw std::runtime_error("Hole index out of bounds");
        }
        if (!holeOptions.at(hole).get(assignment)) {
            // This choice is not possible
            return false;
        }
    }
    return true;
}

template <typename ValueType>
void MatrixGenerator<ValueType>::buildSubModel(
    const storm::storage::BitVector& abstractedHoles,
    const std::vector<storm::storage::BitVector>& holeOptions,
    const std::optional<storm::storage::BitVector>& reachableStatesFixed
) {
    auto const& completeTransitionMatrix = quotient.getTransitionMatrix();

    storm::storage::BitVector includeRowBitVector(decisionMatrix.getRowCount(), false);
    storm::storage::BitVector reachableStates(decisionMatrix.getColumnCount(), false);

    // If we are given a fixed set of reachable states, we can skip the BFS
    // Otherwise, perform a BFS to find the reachable states
    if (!reachableStatesFixed) {
        std::vector<uint64_t> bfsOrder;
        std::queue<uint64_t> statesToProcess;
        for (auto const& initialState : this->quotient.getInitialStates()) {
            reachableStates.set(initialState, true);
            statesToProcess.push(initialState);
        }

        while (!statesToProcess.empty()) {
            auto state = statesToProcess.front();
            statesToProcess.pop();

            // This row group in the quotient (this is what the includedChoices BitVector is based on)
            auto rowGroupStartQuotient = completeTransitionMatrix.getRowGroupIndices()[state];
            auto rowGroupEndQuotient = completeTransitionMatrix.getRowGroupIndices()[state + 1];
            // This row group in the decision matrix (this is what our includeRowBitVector is based on)
            auto rowGroupStartDecision = decisionMatrix.getRowGroupIndices()[state];
            auto rowGroupEndDecision = decisionMatrix.getRowGroupIndices()[state + 1];

            bool someChoiceIncluded = false;
            for (uint64_t row = rowGroupStartQuotient; row < rowGroupEndQuotient; ++row) {
                if (isChoicePossible(abstractedHoles, holeOptions, row)) {
                    someChoiceIncluded = true;

                    // Include this choice
                    if (rowGroupStartDecision + (row - rowGroupStartQuotient) >= includeRowBitVector.size()) {
                        throw std::runtime_error("Row group start decision out of bounds");
                    }
                    includeRowBitVector.set(rowGroupStartDecision + (row - rowGroupStartQuotient), true);
                    // BFS order is over the rows of the original matrix
                    bfsOrder.push_back(row);

                    // Successors of this choice are reachable
                    for (auto const& entry : completeTransitionMatrix.getRow(row)) {
                        if (!reachableStates.get(entry.getColumn()) && entry.getValue() != storm::utility::zero<ValueType>()) {
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

        currentBFSOrder = bfsOrder;
    } else {
        if (reachableStatesFixed->size() != decisionMatrix.getColumnCount()) {
            throw std::runtime_error("Invalid size of reachable states");
        }
        reachableStates = *reachableStatesFixed;
        // We still need to figure out the includeRowBitVector
        for (auto const& state : reachableStates) {
            if (state >= completeTransitionMatrix.getColumnCount()) {
                if (state >= decisionMatrix.getColumnCount()) {
                    throw std::runtime_error("Invalid state in reachable states");
                }
                // This is the last two columns
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
                if (isChoicePossible(abstractedHoles, holeOptions, row)) {
                    someChoiceIncluded = true;
                    // Include this choice
                    if (rowGroupStartDecision + (row - rowGroupStartQuotient) >= includeRowBitVector.size()) {
                        throw std::runtime_error("Row group start decision out of bounds");
                    }
                    includeRowBitVector.set(rowGroupStartDecision + (row - rowGroupStartQuotient), true);
                }
            }
            if (!someChoiceIncluded) {
                // No choice is included, so we need to include the last row of the row group
                includeRowBitVector.set(rowGroupEndDecision - 1, true);
            }
        }

        // Always include the last two columns
        for (std::size_t i = 1; i <= 2; ++i) {
            includeRowBitVector.set(decisionMatrix.getRowCount() - i, true);
        }

        currentBFSOrder = std::nullopt;
    }

    auto const& submatrix = decisionMatrix.getSubmatrix(false, includeRowBitVector, reachableStates, false);

    storm::models::sparse::StateLabeling stateLabeling(submatrix.getColumnCount());
    stateLabeling.addLabel("counterexample_target");

    auto reachableStatesIterator = reachableStates.begin();
    for (std::size_t state = 0; state < submatrix.getColumnCount() - 2; ++state) {
        for (const auto& label : this->quotient.getLabelsOfState(*reachableStatesIterator)) {
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
    
    currentMDP = storm::models::sparse::Mdp<ValueType>(modelComponents);
    currentReachableStates = reachableStates;
}

template <typename ValueType>
const storm::models::sparse::Mdp<ValueType>& MatrixGenerator<ValueType>::getCurrentMDP() const {
    return *this->currentMDP;
}

template <typename ValueType>
const storm::storage::BitVector& MatrixGenerator<ValueType>::getCurrentReachableStates() const {
    return *this->currentReachableStates;
}

template <typename ValueType>
const std::vector<uint64_t>& MatrixGenerator<ValueType>::getCurrentBFSOrder() const {
    return *this->currentBFSOrder;
}

template class MatrixGenerator<double>;
template class MatrixGenerator<storm::RationalFunction>;
