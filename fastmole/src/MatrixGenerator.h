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
    MatrixGenerator<ValueType>(const storm::models::sparse::Mdp<ValueType>& quotient, storm::storage::BitVector targetStates, const std::vector<ValueType>& globalBounds);

    /**
     * @brief Builds a sub-model of the decision matrix, representing an MDP
     * with holes.
     * 
     * @param quotientStateMap 
     * @param includedChoices A BitVector representing which choices (=rows in the original MDP) are included in the submatrix.
     * @return void
     */
    void buildSubModel(
        const storm::storage::BitVector includedChoices
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

    std::optional<storm::models::sparse::Mdp<ValueType>> currentMDP;
    std::optional<storm::storage::BitVector> currentReachableStates;
    std::optional<std::vector<uint64_t>> currentBFSOrder;

    storm::models::sparse::Mdp<ValueType> quotient;
    storm::storage::BitVector targetStates;
    std::vector<ValueType> globalBounds;
    storm::storage::SparseMatrix<ValueType> decisionMatrix;
};
