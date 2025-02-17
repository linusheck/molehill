#include <_types/_uint64_t.h>
#include <unordered_set>
#include "utils.h"

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

std::pair<std::vector<uint64_t>, std::vector<uint64_t>> holeOrder(const std::vector<uint64_t> &bfsOrder,
                                                                  const std::vector<std::vector<std::pair<uint64_t, uint64_t>>> &choiceToAssignment,
                                                                  const std::set<uint64_t> &possibleHoles) {
    std::vector<uint64_t> order;
    std::unordered_set<uint64_t> seen;

    for (uint64_t state : bfsOrder) {
        for (auto const &[hole, _assignment] : choiceToAssignment[state]) {
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

    return {order, holesNotInOrder};
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
template storm::modelchecker::ExplicitModelCheckerHint<double> hintConvert(const std::vector<double> &result, const storm::storage::BitVector &oldReachableStates, const storm::storage::BitVector &newReachableStates);

template<typename ValueType>
storm::modelchecker::ExplicitModelCheckerHint<ValueType> setEndComponentsTrue(const storm::modelchecker::ExplicitModelCheckerHint<ValueType> &hint) {
    storm::modelchecker::ExplicitModelCheckerHint<ValueType> newHint = hint;
    newHint.setNoEndComponentsInMaybeStates(true);
    return newHint;
}
template storm::modelchecker::ExplicitModelCheckerHint<double> setEndComponentsTrue(const storm::modelchecker::ExplicitModelCheckerHint<double> &hint);