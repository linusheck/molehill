#include "utils.h"
#include <storm/storage/BitVector.h>
#include <unordered_set>

/**
 * @brief Get possible choices for a given set of abstracted holes
 *
 * @param choiceToAssignment
 * @param abstractedHoles
 * @param holeOptions
 * @return storm::storage::BitVector
 */
storm::storage::BitVector getPossibleChoices(const std::vector<std::vector<std::pair<int, int>>> &choiceToAssignment,
                                             const storm::storage::BitVector &abstractedHoles, const std::vector<storm::storage::BitVector> &holeOptions) {
    storm::storage::BitVector selectedChoices(choiceToAssignment.size(), false);
    uint64_t choice = 0;
    for (auto const &holeToAssignment : choiceToAssignment) {
        bool possible = true;
        bool holeAbstracted = false;
        for (auto const &[hole, assignment] : holeToAssignment) {
            if (abstractedHoles.get(hole)) {
                holeAbstracted = true;
                break;
            }
            if (!holeOptions[hole].get(assignment)) {
                possible = false;
                break;
            }
        }
        if (holeAbstracted) {
            selectedChoices.set(choice, false);
        } else {
            selectedChoices.set(choice, possible);
        }
        choice++;
    }
    return selectedChoices;
}

template<typename ValueType>
storm::modelchecker::ExplicitModelCheckerHint<ValueType> hintConvert(const std::vector<ValueType> &result, const storm::storage::BitVector &oldReachableStates,
                                                                     const storm::storage::BitVector &newReachableStates) {
    assert(oldReachableStates.getNumberOfSetBits() == result.size());

    std::vector<double> hintValues(newReachableStates.getNumberOfSetBits());
    for (uint64_t state : newReachableStates) {
        if (oldReachableStates[state]) {
            hintValues.push_back(result.at(oldReachableStates.getNumberOfSetBitsBeforeIndex(state)));
        } else {
            hintValues.push_back(storm::utility::zero<ValueType>());
        }
    }

    storm::modelchecker::ExplicitModelCheckerHint<ValueType> hint;
    hint.setResultHint(hintValues);
    hint.setNoEndComponentsInMaybeStates(true);
    return hint;
}
template storm::modelchecker::ExplicitModelCheckerHint<double> hintConvert(const std::vector<double> &result,
                                                                           const storm::storage::BitVector &oldReachableStates,
                                                                           const storm::storage::BitVector &newReachableStates);

template<typename ValueType>
storm::modelchecker::ExplicitModelCheckerHint<ValueType> setEndComponentsTrue(const storm::modelchecker::ExplicitModelCheckerHint<ValueType> &hint) {
    storm::modelchecker::ExplicitModelCheckerHint<ValueType> newHint = hint;
    newHint.setNoEndComponentsInMaybeStates(true);
    return newHint;
}
template storm::modelchecker::ExplicitModelCheckerHint<double> setEndComponentsTrue(const storm::modelchecker::ExplicitModelCheckerHint<double> &hint);

storm::storage::BitVector intersect(const storm::storage::BitVector &a, const storm::storage::BitVector &b) {
    if (a.size() != b.size()) {
        throw std::runtime_error("BitVectors must have the same size");
    }
    storm::storage::BitVector result(a.size(), false);
    for (uint64_t i = 0; i < a.size(); ++i) {
        result.set(i, a.get(i) && b.get(i));
    }
    return result;
}
