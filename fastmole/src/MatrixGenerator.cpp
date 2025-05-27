#include "MatrixGenerator.h"
#include <optional>
#include <queue>
#include <stdexcept>
#include <storm/adapters/RationalFunctionAdapter_Private.h>
#include <storm/adapters/RationalNumberForward.h>
#include <storm/models/sparse/StandardRewardModel.h>
#include <storm/solver/OptimizationDirection.h>
#include <storm/storage/BitVector.h>
#include <storm/storage/sparse/ModelComponents.h>
#include <storm/utility/constants.h>
#include <storm/utility/graph.h>
#include <storm/utility/macros.h>
#include <string>
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

    this->currentAbstractedHoles = abstractedHoles;
    this->currentHoleOptions = holeOptions;

    storm::storage::BitVector includeRowBitVector(decisionMatrix.getRowCount(), false);
    storm::storage::BitVector reachableStates(decisionMatrix.getColumnCount(), false);

    // If we are given a fixed set of reachable states, we can skip the BFS
    // Otherwise, perform a BFS to find the reachable states
    if (!reachableStatesFixed) {
        std::vector<uint64_t> bfsOrder;
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
std::optional<std::vector<uint64_t>> MatrixGenerator<ValueType>::isSchedulerConsistent(const storm::storage::Scheduler<ValueType> &scheduler) {
    // std::cout << "Checking consistency of scheduler" << std::endl;
    if (!this->currentReachableStates) {
        throw std::runtime_error("Call this after buildSubModel");
    }
    std::vector<uint64_t> holeAssignments(this->currentHoleOptions->size(), -1);

    // The states that are not reachable under the scheduler are irrelevant for
    // the consistency check, so we keep track of the reachable states
    storm::storage::BitVector visitedStates(this->currentMDP->getTransitionMatrix().getColumnCount(), false);
    // Set the two last columns to visited, as these are the last two columns which we ignore
    visitedStates.set(visitedStates.size() - 1, true);
    visitedStates.set(visitedStates.size() - 2, true);

    std::queue<uint64_t> statesToProcess;
    for (auto const& initialState : this->currentMDP->getInitialStates()) {
        statesToProcess.push(initialState);
    }

    while (!statesToProcess.empty()) {
        uint64_t localState = statesToProcess.front();
        statesToProcess.pop();
        uint64_t state = *std::next(this->currentReachableStates->begin(), localState);

        // Because this is BFS order, we can be sure that all predecessors are
        // already reachable
        if (visitedStates.get(localState)) {
            continue;
        }
        visitedStates.set(localState, true);
        if (state >= this->quotient.getTransitionMatrix().getColumnCount()) {
            throw std::runtime_error("Invalid state in reachable states: " + std::to_string(state) + " (size: " + std::to_string(this->decisionMatrix.getColumnCount()) + ")");
        }

        // std::cout << "Reachable: "<< state << " (local) " << localState << std::endl;

        // Get the choice taken by the scheduler
        auto const& choice = scheduler.getChoice(localState);
        if (!choice.isDeterministic()) {
            std::cout << "Scheduler must be deterministic" << std::endl;
            return std::nullopt;
        }
        uint64_t deterministicChoice = choice.getDeterministicChoice();
        
        uint64_t localRow = this->currentMDP->getTransitionMatrix().getRowGroupIndices()[localState];
        uint64_t localRowEnd = this->currentMDP->getTransitionMatrix().getRowGroupIndices()[localState + 1];

        if (localRow + deterministicChoice >= localRowEnd) {
            throw std::runtime_error("Local choice index " + std::to_string(deterministicChoice) + " out of bounds (size: " + std::to_string(localRowEnd - localRow) + ")");
        }

        // Visit states reachable under the scheduler
        for (auto const& entry : this->currentMDP->getTransitionMatrix().getRow(localRow + deterministicChoice)) {
            if (!visitedStates.get(entry.getColumn()) && entry.getValue() != storm::utility::zero<ValueType>()) {
                statesToProcess.push(entry.getColumn());
            }
        }

        uint64_t row = this->quotient.getTransitionMatrix().getRowGroupIndices()[state];
        uint64_t rowEnd = this->quotient.getTransitionMatrix().getRowGroupIndices()[state + 1];

        // We need to get the global choice
        // E.g. My hole options are 1101101 and my deterministic choice is 3
        // Then the global choice is actually 4 (the fourth set bit)
        uint64_t globalChoice = -1;
        uint64_t localChoiceTmp = deterministicChoice + 1;
        while (localChoiceTmp > 0) {
            globalChoice++;
            if (row + globalChoice >= rowEnd) {
                throw std::runtime_error("Global choice index out of bounds");
            }
            if (isChoicePossible(*this->currentAbstractedHoles, *this->currentHoleOptions, row + globalChoice)) {
                // std::cout << "Possible choice " << globalChoice << std::endl;
                localChoiceTmp--;
            } else {
                // std::cout << "Impossible choice " << globalChoice << std::endl;
            }
        }

        if (row + globalChoice >= rowEnd) {
            // std::cout << "Local state " << localState  << " global state " << state << " global choice " << globalChoice << std::endl;
            throw std::runtime_error("Choice index " + std::to_string(globalChoice) + " out of bounds (size: " + std::to_string(rowEnd - row) + ")");
        }

        auto const& assignment = choiceToAssignment[row + globalChoice];

        for (auto const& [hole, assignment] : assignment) {
            if (holeAssignments[hole] != -1) {
                if (holeAssignments[hole] != assignment) {
                    // The scheduler is inconsistent
                    // std::cout << "Inconsistent hole " << hole << " assignment " << assignment << std::endl;
                    return std::nullopt;
                }
            } else {
                // std::cout << "Hole " << hole << " assignment " << assignment << std::endl;
                // std::cout << "Local choice " << deterministicChoice << " global choice " << globalChoice << std::endl;
                holeAssignments[hole] = assignment;
            }
        }
    }
    // std::cout << "Consistent" << std::endl;
    // std::ofstream outFile("out.dot");
    // if (!outFile.is_open()) {
    //     throw std::runtime_error("Failed to open file out.dot for writing");
    // }
    // this->currentMDP->writeDotToStream(outFile);
    // outFile.close();
    // scheduler.printToStream(std::cout);
    return holeAssignments;
}

template<typename ValueType>
storm::storage::BitVector MatrixGenerator<ValueType>::optimalAssignments(const storm::storage::Scheduler<ValueType> &scheduler, const std::vector<ValueType> &values, storm::OptimizationDirection optimizationDirection) {
    if (!this->currentReachableStates) {
        throw std::runtime_error("No reachable states");
    }

    // Optimal assignments start at the abstracted holes
    storm::storage::BitVector optimalAssignments(this->currentHoleOptions->size(), true);
    // std::cout << "Optimal assignments: " << optimalAssignments << std::endl;
    uint64_t counter = -1;

    for (auto const& state : *this->currentReachableStates) {
        counter++;
        if (this->quotient.getTransitionMatrix().getRowGroupSize(state) <= 1) {
            // This state has only one choice, so there is no need to check
            continue;
        }

        if (state >= this->quotient.getTransitionMatrix().getColumnCount()) {
            if (state >= this->decisionMatrix.getColumnCount()) {
                throw std::runtime_error("Invalid state in reachable states");
            }
            // This is the last two columns
            continue;
        }

        uint64_t row = this->quotient.getTransitionMatrix().getRowGroupIndices()[state];
        uint64_t rowEnd = this->quotient.getTransitionMatrix().getRowGroupIndices()[state + 1];

        // TODO I think this is bugged, what has the scheduler got to do with this?
        auto const& choice = scheduler.getChoice(counter);
        if (!choice.isDeterministic()) {
            throw std::runtime_error("Scheduler must be deterministic");
        }
        uint64_t deterministicChoice = choice.getDeterministicChoice();
        
        // Why should this be correct? E.g. if I filter a couple rows??
        if (row + deterministicChoice >= rowEnd) {
            throw std::runtime_error("Row " + std::to_string(row) + " of " + std::to_string(this->quotient.getTransitionMatrix().getRowCount()) + " Choice index " + std::to_string(deterministicChoice) + " out of bounds (size: " + std::to_string(rowEnd - row) + ")");
        }

        // Check if there is still a hole here that is considered optimal
        bool holeOptimal = false;
        for (auto const& [hole, _assignment] : this->choiceToAssignment[row + deterministicChoice]) {
            if (optimalAssignments.get(hole)) {
                // This hole is still considered optimal
                holeOptimal = true;
                continue;
            }
        }
        if (!holeOptimal) {
            // No hole is considered optimal here
            continue;
        }

        // std::cout << "Optimal assignments " << optimalAssignments << std::endl;
        // Print involved holes
        // std::cout << "Involved holes: ";
        // for (auto const& [hole, assignment] : choiceToAssignment[row + deterministicChoice]) {
        //     std::cout << hole << " ";
        // }
        // std::cout << std::endl;

        // The result in the sub-MDP. This must be "better"
        const ValueType resultHere = values[counter];

        // std::cout << resultHere << " vs ";
        
        for (uint64_t otherRow = row; otherRow < rowEnd; otherRow++) {
            if (otherRow == row + deterministicChoice) {
                // This is the choice that was taken
                continue;
            }
            if (isChoicePossible(*this->currentAbstractedHoles, *this->currentHoleOptions, otherRow)) {
                continue;
            }
            ValueType otherResult = storm::utility::zero<ValueType>();
            for (auto const& entry : this->quotient.getTransitionMatrix().getRow(otherRow)) {
                otherResult += entry.getValue() * globalBounds[entry.getColumn()];
            }
            // std::cout << otherResult << " ";
            if (optimizationDirection == storm::OptimizationDirection::Maximize) {
                if (otherResult > resultHere) {
                    // Are there conflicting assignments here?
                    // TODO Possible generalization: Can we still keep the hole if the assignment is the same?
                    for (auto const& [conflictingHole, _assignment] : choiceToAssignment[row + deterministicChoice]) {
                        optimalAssignments.set(conflictingHole, false);
                    }
                }
            } else {
                if (otherResult < resultHere) {
                    // Are there conflicting assignments here?
                    // TODO Possible generalization: Can we still keep the hole if the assignment is the same?
                    for (auto const& [conflictingHole, _assignment] : choiceToAssignment[row + deterministicChoice]) {
                        optimalAssignments.set(conflictingHole, false);
                    }
                }
            }
        }
        // std::cout << std::endl;
    }
    return optimalAssignments;
}

template class MatrixGenerator<double>;
template class MatrixGenerator<storm::RationalNumber>;
