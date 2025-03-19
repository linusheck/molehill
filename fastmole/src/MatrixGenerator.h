#pragma once
#include <map>
#include <optional>
#include <storm/modelchecker/CheckTask.h>
#include <storm/storage/Scheduler.h>
#include <vector>
#include "storm/adapters/RationalFunctionAdapter.h"
#include "storm/models/sparse/Mdp.h"
#include "storm/models/sparse/StateLabeling.h"
#include "storm/storage/BitVector.h"
#include "storm/storage/SparseMatrix.h"
#include "storm/utility/constants.h"
#include "storm/utility/graph.h"

template<typename ValueType>
class MatrixGenerator {
   public:
    /**
     * @brief Construct a new Matrix Generator object
     *
     * @param quotient The quotient MDP.
     * @param checkTask The check task.
    * @param targetStates The target states.
    * @param globalBounds An initial model checking result on the quotient MDP.
    * @param choiceToAssignment The mapping from choices (in quotient MDP) to assignments (of PAYNT variables).
     */
    MatrixGenerator(const storm::models::sparse::Mdp<ValueType> &quotient, const storm::modelchecker::CheckTask<storm::logic::Formula, ValueType> &checkTask,
                    const storm::storage::BitVector &targetStates, const std::vector<ValueType> &globalBounds,
                    const std::vector<std::vector<std::pair<int, int>>> &choiceToAssignment);

    /**
     * @brief Builds a sub-model of the decision matrix, representing an MDP *
     * with holes. Call the get-functions to retrieve the results of the call.
     *
     * @param abstractedHoles abstracedHoles[i] is true if the hole i is deleted (as in a counterexample candidate), false if it is not deleted.
     * @param holeOptions holeOptions[i] is a bit vector representing the possible choices for hole i.
     * @param reachableStatesFixed If given, the reachable states are fixed to this value. Currently not supported.
     * @return void
     */
    void buildSubModel(const storm::storage::BitVector &abstractedHoles, const std::vector<storm::storage::BitVector> &holeOptions,
                       const std::optional<storm::storage::BitVector> &reachableStatesFixed = std::nullopt);

    /**
     * @brief Get the current MDP
     *
     * @return const storm::models::sparse::Mdp<ValueType>&
     */
    const storm::models::sparse::Mdp<ValueType> &getCurrentMDP() const;

    /**
     * @brief Get the current reachable states
     *
     * @return const storm::storage::BitVector&
     */
    const storm::storage::BitVector &getCurrentReachableStates() const;

    /**
     * @brief Get the current BFS order
     *
     * @return const std::vector<uint64_t>&
     */
    const std::vector<uint64_t> &getCurrentBFSOrder() const;

    /**
     * @brief Builds the order that the holes are visited in the BFS order.
     * TODO: Somehow mark holes that always appear at the same time.
     * 
     * @param bfsOrder BFS order of the MDP.
     * @param possibleHoles Holes to look for.
     * @return std::pair<std::vector<uint64_t>, std::vector<uint64_t>> hole order, holes that are not reachable
     */
    std::pair<std::vector<uint64_t>, std::vector<uint64_t>> holeOrder(const std::vector<uint64_t> &bfsOrder,
                                                                      const std::set<uint64_t> &possibleHoles);

    /**
     * @brief Is the scheduler consistent with the hole order?
     * Uses current reachable states.
     * 
     * @param scheduler The MDP scheduler.
     * @return true The scheduler is consistent.
     * @return false The scheduler is inconsistent.
     */
    bool isSchedulerConsistent(const storm::storage::Scheduler<ValueType> &scheduler);

    /**
     * @brief Are some holes in this scheduler already optimal?
     * 
     * @param scheduler The MDP scheduler.
     * @return BitVector the holes in this scheduler that are already optimal.
     */
    storm::storage::BitVector optimalAssignments(const storm::storage::Scheduler<ValueType> &scheduler, const std::vector<ValueType> &values, storm::OptimizationDirection optimizationDirection);

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
     * @brief Checks if a choice is possible given the abstracted holes and hole
     * options.
     *
     * @param abstractedHoles
     * @param holeOptions
     * @param choice
     * @return bool
     */
    bool isChoicePossible(const storm::storage::BitVector &abstractedHoles, const std::vector<storm::storage::BitVector> &holeOptions, uint64_t choice);

    std::optional<storm::models::sparse::Mdp<ValueType>> currentMDP;
    std::optional<storm::storage::BitVector> currentReachableStates;
    std::optional<std::vector<uint64_t>> currentBFSOrder;

    std::optional<storm::storage::BitVector> currentAbstractedHoles;
    std::optional<std::vector<storm::storage::BitVector>> currentHoleOptions;

    std::vector<std::vector<std::pair<int, int>>> choiceToAssignment;
    storm::models::sparse::Mdp<ValueType> quotient;
    storm::storage::BitVector targetStates;
    std::vector<ValueType> globalBounds;
    storm::storage::SparseMatrix<ValueType> decisionMatrix;
    std::optional<std::vector<ValueType>> rewards;
    storm::modelchecker::CheckTask<storm::logic::Formula, ValueType> checkTask;
};
