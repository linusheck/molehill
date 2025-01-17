#pragma once
#include "storm/adapters/RationalFunctionAdapter.h"
#include "storm/storage/SparseMatrix.h"
#include "storm/storage/BitVector.h"
#include "storm/utility/graph.h"
#include "storm/utility/constants.h"
#include "storm/models/sparse/StateLabeling.h"


template <typename ValueType>
class MatrixGenerator {
public:
    MatrixGenerator<ValueType>(const storm::storage::SparseMatrix<ValueType>& completeTransitionMatrix, const std::vector<ValueType>& globalBounds);

    storm::storage::SparseMatrix<ValueType> buildMatrix(
        const std::vector<uint64_t> quotientStateMap,
        const storm::storage::SparseMatrix<ValueType>& subMdpMatrix,
        const std::set<uint64_t> includedChoices
    );

    storm::models::sparse::StateLabeling buildStateLabeling(
        const storm::storage::SparseMatrix<ValueType>& subMdpMatrix,
        const storm::models::sparse::StateLabeling& subMdpLabeling,
        const std::vector<std::size_t>& oneStates
    );

private:
    storm::storage::SparseMatrix<ValueType> buildDecisionMatrix();

    storm::storage::SparseMatrix<ValueType> completeTransitionMatrix;
    std::vector<ValueType> globalBounds;
    storm::storage::SparseMatrix<ValueType> decisionMatrix;
};
