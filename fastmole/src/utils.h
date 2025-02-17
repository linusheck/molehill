#pragma once

#include <vector>
#include <unordered_set>
#include "storm/storage/BitVector.h"
#include "storm/modelchecker/hints/ExplicitModelCheckerHint.h"

storm::storage::BitVector getPossibleChoices(
    const std::vector<std::vector<std::pair<int, int>>> &choiceToAssignment,
    const storm::storage::BitVector &abstractedHoles,
    const std::vector<storm::storage::BitVector> &holeOptions);

std::pair<std::vector<uint64_t>, std::vector<uint64_t>> holeOrder(
    const std::vector<uint64_t> &bfsOrder,
    const std::vector<std::vector<std::pair<uint64_t, uint64_t>>> &choiceToAssignment,
    const std::set<uint64_t> &possibleHoles);

template<typename ValueType>
storm::modelchecker::ExplicitModelCheckerHint<ValueType> hintConvert(
    const std::vector<ValueType> &result,
    const storm::storage::BitVector &oldReachableStates,
    const storm::storage::BitVector &newReachableStates);

template<typename ValueType>
storm::modelchecker::ExplicitModelCheckerHint<ValueType> setEndComponentsTrue(
    const storm::modelchecker::ExplicitModelCheckerHint<ValueType> &hint);
