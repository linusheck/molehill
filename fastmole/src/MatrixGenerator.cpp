
#include "MatrixGenerator.h"
#include <optional>
#include <queue>
#include <stdexcept>
#include <storm/adapters/RationalNumberForward.h>
#include <storm/models/sparse/StandardRewardModel.h>
#include <storm/storage/BitVector.h>
#include <storm/storage/sparse/ModelComponents.h>
#include <storm/utility/constants.h>
#include <storm/utility/macros.h>
#include <vector>

template<typename ValueType>
MatrixGenerator<ValueType>::MatrixGenerator(const storm::models::sparse::Mdp<ValueType> &quotient,
                                            const storm::modelchecker::CheckTask<storm::logic::Formula, ValueType> &checkTask,
                                            const storm::storage::BitVector &targetStates, const std::vector<ValueType> &globalBounds,
                                            const std::vector<std::vector<std::pair<int, int>>> &choiceToAssignment)
    : quotient(quotient), checkTask(checkTask), targetStates(targetStates), globalBounds(globalBounds), choiceToAssignment(choiceToAssignment) {
    if (this->rewards && this->rewards->size() != this->decisionMatrix.getRowCount()) {
        throw std::runtime_error("Invalid size of rewards");
    }
    this->decisionMatrix = buildDecisionMatrix();
}

template<typename ValueType>
storm::storage::SparseMatrix<ValueType> MatrixGenerator<ValueType>::buildDecisionMatrix() {
    auto const &completeTransitionMatrix = quotient.getTransitionMatrix();
    storm::storage::SparseMatrixBuilder<ValueType> builder(0, 0, 0, true, true);
    auto zeroState = completeTransitionMatrix.getColumnCount();
    auto oneState = completeTransitionMatrix.getColumnCount() + 1;
    std::size_t newRowCounter = 0;

    if (!(checkTask.getFormula().isRewardOperatorFormula() || checkTask.getFormula().isProbabilityOperatorFormula())) {
        throw std::runtime_error("Formula must be a reward or reachability formula");
    }
    bool checkRewards = checkTask.getFormula().isRewardOperatorFormula();

    std::optional<std::vector<ValueType>> stateActionRewardVector;
    if (checkRewards) {
        auto const &rewardModel = quotient.getRewardModel(checkTask.getRewardModel());
        if (!rewardModel.hasStateActionRewards()) {
            throw std::runtime_error("Reward model must only have state actions rewards");
        }
        stateActionRewardVector = rewardModel.getStateActionRewardVector();
        if (stateActionRewardVector->size() != completeTransitionMatrix.getRowCount()) {
            throw std::runtime_error("Invalid size of state rewards");
        }
        this->rewards = std::vector<ValueType>();
    }

    // The decision matrix has one additional row and column for the hole
    // inclusion.
    for (std::size_t state = 0; state < completeTransitionMatrix.getColumnCount(); ++state) {
        auto rowGroupStart = completeTransitionMatrix.getRowGroupIndices()[state];
        auto rowGroupEnd = completeTransitionMatrix.getRowGroupIndices()[state + 1];
        builder.newRowGroup(newRowCounter);
        for (std::size_t row = rowGroupStart; row < rowGroupEnd; ++row) {
            for (const auto &entry : completeTransitionMatrix.getRow(row)) {
                builder.addNextValue(newRowCounter, entry.getColumn(), entry.getValue());
            }
            if (this->rewards) {
                this->rewards->push_back(stateActionRewardVector->at(row));
            }
            ++newRowCounter;
        }
        if (this->rewards) {
            builder.addNextValue(newRowCounter, oneState, storm::utility::one<ValueType>());
            this->rewards->push_back(globalBounds[state]);
        } else {
            builder.addNextValue(newRowCounter, zeroState, storm::utility::one<ValueType>() - globalBounds[state]);
            builder.addNextValue(newRowCounter, oneState, globalBounds[state]);
        }
        ++newRowCounter;
    }
    builder.newRowGroup(newRowCounter);
    builder.addNextValue(newRowCounter, zeroState, storm::utility::one<ValueType>());
    builder.newRowGroup(newRowCounter + 1);
    builder.addNextValue(newRowCounter + 1, oneState, storm::utility::one<ValueType>());

    if (this->rewards) {
        this->rewards->push_back(storm::utility::zero<ValueType>());
        this->rewards->push_back(storm::utility::zero<ValueType>());
    }

    return builder.build();
}

template<typename ValueType>
bool MatrixGenerator<ValueType>::isChoicePossible(const storm::storage::BitVector &abstractedHoles, const std::vector<storm::storage::BitVector> &holeOptions,
                                                  uint64_t choice) {
    if (choice >= this->choiceToAssignment.size()) {
        throw std::runtime_error("Choice index " + std::to_string(choice) + " out of bounds (size: " + std::to_string(this->choiceToAssignment.size()) + ")");
    }
    for (auto const &[hole, assignment] : this->choiceToAssignment.at(choice)) {
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

template<typename ValueType>
void MatrixGenerator<ValueType>::buildSubModel(const storm::storage::BitVector &abstractedHoles, const std::vector<storm::storage::BitVector> &holeOptions,
                                               const std::optional<storm::storage::BitVector> &reachableStatesFixed) {
    auto const &completeTransitionMatrix = quotient.getTransitionMatrix();

    storm::storage::BitVector includeRowBitVector(decisionMatrix.getRowCount(), false);
    storm::storage::BitVector reachableStates(decisionMatrix.getColumnCount(), false);

    // If we are given a fixed set of reachable states, we can skip the BFS
    // Otherwise, perform a BFS to find the reachable states
    if (!reachableStatesFixed) {
        std::vector<uint64_t> bfsOrder(decisionMatrix.getRowCount());
        std::queue<uint64_t> statesToProcess;
        for (auto const &initialState : this->quotient.getInitialStates()) {
            reachableStates.set(initialState, true);
            statesToProcess.push(initialState);
        }

        while (!statesToProcess.empty()) {
            auto state = statesToProcess.front();
            statesToProcess.pop();

            // This row group in the quotient (this is what the includedChoices
            // BitVector is based on)
            auto rowGroupStartQuotient = completeTransitionMatrix.getRowGroupIndices()[state];
            auto rowGroupEndQuotient = completeTransitionMatrix.getRowGroupIndices()[state + 1];
            // This row group in the decision matrix (this is what our
            // includeRowBitVector is based on)
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
                    for (auto const &entry : completeTransitionMatrix.getRow(row)) {
                        if (!reachableStates.get(entry.getColumn()) && entry.getValue() != storm::utility::zero<ValueType>()) {
                            reachableStates.set(entry.getColumn(), true);
                            statesToProcess.push(entry.getColumn());
                        }
                    }
                }
            }
            if (!someChoiceIncluded) {
                // No choice is included, so we need to include the last row of the row
                // group
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
        // WARNING: I'm not using this code path right now, it might be broken.
        // I still think it's a good idea to keep it around for now.
        throw std::runtime_error("Using fixed reachable states is not supported right now");
        if (reachableStatesFixed->size() != decisionMatrix.getColumnCount()) {
            throw std::runtime_error("Invalid size of reachable states");
        }
        reachableStates = *reachableStatesFixed;
        // We still need to figure out the includeRowBitVector
        for (auto const &state : reachableStates) {
            if (state >= completeTransitionMatrix.getColumnCount()) {
                if (state >= decisionMatrix.getColumnCount()) {
                    throw std::runtime_error("Invalid state in reachable states");
                }
                // This is the last two columns
                continue;
            }
            // This row group in the quotient (this is what the includedChoices
            // BitVector is based on)
            auto rowGroupStartQuotient = completeTransitionMatrix.getRowGroupIndices()[state];
            auto rowGroupEndQuotient = completeTransitionMatrix.getRowGroupIndices()[state + 1];
            // This row group in the decision matrix (this is what our
            // includeRowBitVector is based on)
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
                // No choice is included, so we need to include the last row of the row
                // group
                includeRowBitVector.set(rowGroupEndDecision - 1, true);
            }
        }

        // Always include the last two columns
        for (std::size_t i = 1; i <= 2; ++i) {
            includeRowBitVector.set(decisionMatrix.getRowCount() - i, true);
        }

        currentBFSOrder = std::nullopt;
    }

    auto const &submatrix = decisionMatrix.getSubmatrix(false, includeRowBitVector, reachableStates, false);

    storm::models::sparse::StateLabeling stateLabeling(submatrix.getColumnCount());
    stateLabeling.addLabel("counterexample_target");

    auto reachableStatesIterator = reachableStates.begin();
    for (std::size_t state = 0; state < submatrix.getColumnCount() - 2; ++state) {
        for (const auto &label : this->quotient.getLabelsOfState(*reachableStatesIterator)) {
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
    if (this->rewards) {
        // Target is the zeroState (we collect reward at oneState before)
        stateLabeling.addLabelToState("counterexample_target", submatrix.getColumnCount() - 2);
    }
    // Target is the oneState
    stateLabeling.addLabelToState("counterexample_target", submatrix.getColumnCount() - 1);

    std::unordered_map<std::string, storm::models::sparse::StandardRewardModel<ValueType>> rewardModels;
    if (this->rewards) {
        std::vector<ValueType> filteredRewards(submatrix.getRowCount(), storm::utility::zero<ValueType>());
        auto includeIterator = includeRowBitVector.begin();
        for (std::size_t row = 0; row < submatrix.getRowCount(); ++row) {
            filteredRewards[row] = this->rewards->at(*includeIterator);
            includeIterator++;
        }
        storm::models::sparse::StandardRewardModel<ValueType> rewardModel(std::nullopt, filteredRewards);
        rewardModels[checkTask.getRewardModel()] = rewardModel;
    }

    storm::storage::sparse::ModelComponents<ValueType> modelComponents(std::move(submatrix), std::move(stateLabeling), std::move(rewardModels));

    currentMDP = std::move(storm::models::sparse::Mdp<ValueType>(modelComponents));
    currentReachableStates = std::move(reachableStates);
}

template<typename ValueType>
const storm::models::sparse::Mdp<ValueType> &MatrixGenerator<ValueType>::getCurrentMDP() const {
    return *this->currentMDP;
}

template<typename ValueType>
const storm::storage::BitVector &MatrixGenerator<ValueType>::getCurrentReachableStates() const {
    return *this->currentReachableStates;
}

template<typename ValueType>
const std::vector<uint64_t> &MatrixGenerator<ValueType>::getCurrentBFSOrder() const {
    return *this->currentBFSOrder;
}

template<typename ValueType>
std::pair<std::vector<uint64_t>, std::vector<uint64_t>> MatrixGenerator<ValueType>::holeOrder(const std::vector<uint64_t> &bfsOrder,
                                                                                               const std::set<uint64_t> &possibleHoles) {
    std::vector<uint64_t> order;
    std::unordered_set<uint64_t> seen;

    for (uint64_t state : bfsOrder) {
        for (auto const &[hole, _assignment] : this->choiceToAssignment[state]) {
            if (possibleHoles.contains(hole) && seen.insert(hole).second) {
                order.push_back(hole);
            }
        }
    }

    std::vector<uint64_t> holesNotInOrder;
    for (uint64_t hole : possibleHoles) {
        if (!seen.contains(hole)) {
            holesNotInOrder.push_back(hole);
        }
    }

    return std::make_pair(order, holesNotInOrder);
}

template<typename ValueType>
bool MatrixGenerator<ValueType>::isSchedulerConsistent(const storm::storage::Scheduler<ValueType> &scheduler) {
    std::unordered_map<uint64_t, uint64_t> holeAssignments;
    uint64_t counter = 0;
    if (!this->currentReachableStates) {
        throw std::runtime_error("No reachable states");
    }
    for (auto const& state : *this->currentReachableStates) {
        if (state >= this->quotient.getTransitionMatrix().getColumnCount()) {
            if (state >= this->decisionMatrix.getColumnCount()) {
                throw std::runtime_error("Invalid state in reachable states");
            }
            // This is the last two columns
            continue;
        }
        uint64_t row = this->quotient.getTransitionMatrix().getRowGroupIndices()[state];
        uint64_t rowEnd = this->quotient.getTransitionMatrix().getRowGroupIndices()[state + 1];

        auto const& choice = scheduler.getChoice(counter);
        if (!choice.isDeterministic()) {
            throw std::runtime_error("Scheduler must be deterministic");
        }
        uint64_t deterministicChoice = choice.getDeterministicChoice();
        
        if (row + deterministicChoice >= rowEnd) {
            throw std::runtime_error("Choice index " + std::to_string(deterministicChoice) + " out of bounds (size: " + std::to_string(rowEnd - row) + ")");
        }

        auto const& assignment = choiceToAssignment[row + deterministicChoice];

        for (auto const& [hole, assignment] : assignment) {
            if (holeAssignments.contains(hole)) {
                if (holeAssignments[hole] != assignment) {
                    return false;
                }
            } else {
                holeAssignments[hole] = assignment;
            }
        }

        counter++;
    }
    return true;
}

template class MatrixGenerator<double>;
template class MatrixGenerator<storm::RationalNumber>;
