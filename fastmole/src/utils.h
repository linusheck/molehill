#pragma once

#include <unordered_set>
#include <vector>
#include "storm/storage/BitVector.h"

storm::storage::BitVector getPossibleChoices(const std::vector<std::vector<std::pair<int, int>>> &choiceToAssignment,
                                             const storm::storage::BitVector &abstractedHoles, const std::vector<storm::storage::BitVector> &holeOptions);

// /**
// * @brief Convert a hint from one set of reachable states to another.
// * 
// * @param result The hint values.
// * @param oldReachableStates The old reachable states.
// * @param newReachableStates The new reachable states.
// * @return storm::modelchecker::ExplicitModelCheckerHint<ValueType> The new hint.
// */
// template<typename ValueType>
// storm::modelchecker::ExplicitModelCheckerHint<ValueType> hintConvert(const std::vector<ValueType> &result, const storm::storage::BitVector &oldReachableStates,
//                                                                      const storm::storage::BitVector &newReachableStates);

// /**
// * @brief Call setNoEndComponentsInMaybeStates(true) on the hint.
// * 
// * @param hint 
// * @return storm::modelchecker::ExplicitModelCheckerHint<ValueType> 
// */
// template<typename ValueType>
// storm::modelchecker::ExplicitModelCheckerHint<ValueType> setEndComponentsTrue(const storm::modelchecker::ExplicitModelCheckerHint<ValueType> &hint);

/**
 * @brief Intersect two BitVectors.
 * 
 * @param a BitVector a.
 * @param b BitVector b.
 * @return storm::storage::BitVector Their intersection.
 */
storm::storage::BitVector intersect(const storm::storage::BitVector &a, const storm::storage::BitVector &b);