#pragma once

#include <unordered_set>
#include <vector>
#include "storm/modelchecker/hints/ExplicitModelCheckerHint.h"
#include "storm/storage/BitVector.h"

storm::storage::BitVector getPossibleChoices(const std::vector<std::vector<std::pair<int, int>>> &choiceToAssignment,
                                             const storm::storage::BitVector &abstractedHoles, const std::vector<storm::storage::BitVector> &holeOptions);

template<typename ValueType>
storm::modelchecker::ExplicitModelCheckerHint<ValueType> hintConvert(const std::vector<ValueType> &result, const storm::storage::BitVector &oldReachableStates,
                                                                     const storm::storage::BitVector &newReachableStates);

template<typename ValueType>
storm::modelchecker::ExplicitModelCheckerHint<ValueType> setEndComponentsTrue(const storm::modelchecker::ExplicitModelCheckerHint<ValueType> &hint);

storm::storage::BitVector intersect(const storm::storage::BitVector &a, const storm::storage::BitVector &b);