#pragma once
#include <storm/utility/constants.h>
#include <vector>
#include <algorithm>
#include <storm/storage/BitVector.h>
#include <cassert>
#include <vector>
#include <storm/modelchecker/hints/ExplicitModelCheckerHint.h>

/**
 * @brief Get possible choices for a given set of abstracted holes
 * 
 * @param choiceToAssignment 
 * @param abstractedHoles 
 * @param holeOptions 
 * @return storm::storage::BitVector 
 */
storm::storage::BitVector getPossibleChoices(
    const std::vector<std::vector<std::pair<int, int>>>& choiceToAssignment,
    const storm::storage::BitVector& abstractedHoles,
    const std::vector<storm::storage::BitVector>& holeOptions) {
    storm::storage::BitVector selectedChoices(choiceToAssignment.size(), false);
    uint64_t choice = 0;
    for (auto const& holeToAssignment : choiceToAssignment) {
        bool possible = true;
        bool holeAbstracted = false;
        for (auto const& [hole, assignment] : holeToAssignment) {
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
storm::modelchecker::ExplicitModelCheckerHint<ValueType> hintConvert(
    const std::vector<ValueType>& result,
    const storm::storage::BitVector& oldReachableStates,
    const storm::storage::BitVector& newReachableStates) {
    
    assert(oldReachableStates.size() == result.size());
    
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
    return hint;
}
