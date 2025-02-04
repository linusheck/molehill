#pragma once
#include "storm/adapters/RationalFunctionAdapter.h"
#include "storm/storage/SparseMatrix.h"
#include "storm/storage/BitVector.h"
#include "storm/utility/graph.h"
#include "storm/utility/constants.h"
#include "storm/models/sparse/StateLabeling.h"
#include "storm/models/sparse/Mdp.h"
#include <optional>
#include <vector>


template <typename ValueType>
class MatrixGenerator {
public:
    /**
     * @brief Construct a new Matrix Generator object
     * 
     * @param completeTransitionMatrix The quotient MDP's transition matrix. Must be topologically sorted.
     * @param globalBounds 
     */
    MatrixGenerator<ValueType>(
        const storm::models::sparse::Mdp<ValueType>& quotient,
        storm::storage::BitVector targetStates,
        const std::vector<ValueType>& globalBounds,
        const std::vector<std::vector<std::pair<int, int>>>& choiceToAssignment
    );

    /**
     * @brief Builds a sub-model of the decision matrix, representing an MDP * with holes.
     * 
     * @param choiceToAssignment
     * @param abstractedHoles
     * @param holeOptions
     * @return void
     */
     void buildSubModel(
        const storm::storage::BitVector& abstractedHoles,
        const std::vector<storm::storage::BitVector>& holeOptions,
        const std::optional<storm::storage::BitVector>& reachableStatesFixed = std::nullopt
    );

    /**
     * @brief Get the current MDP
     * 
     * @return const storm::models::sparse::Mdp<ValueType>& 
     */
    const storm::models::sparse::Mdp<ValueType>& getCurrentMDP() const;

    /**
     * @brief Get the current reachable states
     * 
     * @return const storm::storage::BitVector& 
     */
    const storm::storage::BitVector& getCurrentReachableStates() const;

    /**
     * @brief Get the current BFS order
     * 
     * @return const std::vector<uint64_t>& 
     */
    const std::vector<uint64_t>& getCurrentBFSOrder() const;

private:
    /**
     * @brief Builds the "decision matrix", which is an internal representation
     * containing the entire MDP's transition matrix, and an additional row and
     * column for hole inclusions.
     * 
     * @return storm::storage::SparseMatrix<ValueType> 
     */
    storm::storage::SparseMatrix<ValueType> buildDecisionMatrix();

    /**
     * @brief Checks if a choice is possible given the abstracted holes and hole options.
     * 
     * @param abstractedHoles 
     * @param holeOptions 
     * @param choice 
     * @return bool 
     */
    bool isChoicePossible(
        const storm::storage::BitVector& abstractedHoles,
        const std::vector<storm::storage::BitVector>& holeOptions,
        uint64_t choice);

    std::optional<storm::models::sparse::Mdp<ValueType>> currentMDP;
    std::optional<storm::storage::BitVector> currentReachableStates;
    std::optional<std::vector<uint64_t>> currentBFSOrder;

    std::vector<std::vector<std::pair<int, int>>> choiceToAssignment;
    storm::models::sparse::Mdp<ValueType> quotient;
    storm::storage::BitVector targetStates;
    std::vector<ValueType> globalBounds;
    storm::storage::SparseMatrix<ValueType> decisionMatrix;
};
