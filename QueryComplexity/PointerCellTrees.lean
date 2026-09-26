import QueryComplexity.OracleTrees
import QueryComplexity.PointerTranscript
import QueryComplexity.PointerDiscoveries

namespace QueryComplexity.PointerDistributions

def cellInput {q : ℕ} (x : PointerInput q) : Fin q × Fin q → PointerCell q :=
  fun coordinate => x coordinate.1 coordinate.2

abbrev CellTree (q : ℕ) (Output : Type*) := OracleTree (Fin q × Fin q) (PointerCell q) Output

def negativeLeaf {q : ℕ} {Output : Type*} (tree : CellTree q Output)
    (reference : Fin q → Fin q) : tree.Leaf := tree.route (cellInput (negative reference))

def negativeLeafQueries {q : ℕ} {Output : Type*} (tree : CellTree q Output)
    (reference : Fin q → Fin q) : Finset (Fin q × Fin q) :=
  tree.queried (negativeLeaf tree reference)

theorem route_negativeLeaf_iff {q : ℕ} {Output : Type*} (tree : CellTree q Output)
    (reference : Fin q → Fin q) (x : PointerInput q) :
    tree.route (cellInput x) = negativeLeaf tree reference ↔
      Observes (negativeLeafQueries tree reference) x (negative reference) :=
  OracleTree.route_eq_reference_iff tree (cellInput (negative reference)) (cellInput x)

noncomputable def negativeLeafProbability {q : ℕ} {Output : Type*}
    (tree : CellTree q Output) (reference : Fin q → Fin q) : ℝ :=
  (Nat.card {hidden : Fin q → Fin q //
    tree.route (cellInput (negative hidden)) = negativeLeaf tree reference} : ℝ) /
      Nat.card (Fin q → Fin q)

noncomputable def positiveLeafProbability {q : ℕ} {Output : Type*}
    (tree : CellTree q Output) (reference : Fin q → Fin q) : ℝ :=
  (Nat.card {sample : PositiveSample q //
    tree.route (cellInput (sampledPositive sample)) = negativeLeaf tree reference} : ℝ) /
      Nat.card (PositiveSample q)

theorem negativeLeafProbability_eq {q : ℕ} {Output : Type*}
    (tree : CellTree q Output) (reference : Fin q → Fin q) :
    negativeLeafProbability tree reference =
      negativeObservationProbability (negativeLeafQueries tree reference) reference := by
  unfold negativeLeafProbability negativeObservationProbability
  simp only [route_negativeLeaf_iff]

theorem positiveLeafProbability_eq {q : ℕ} {Output : Type*}
    (tree : CellTree q Output) (reference : Fin q → Fin q) :
    positiveLeafProbability tree reference =
      positiveObservationProbability (negativeLeafQueries tree reference) reference := by
  unfold positiveLeafProbability positiveObservationProbability
  simp only [route_negativeLeaf_iff]

/-- Exact likelihood ratio for an actual adaptive full-cell tree leaf. -/
theorem cellTree_likelihood_ratio {q : ℕ} {Output : Type*} (hq : 2 ≤ q)
    (tree : CellTree q Output) (reference : Fin q → Fin q) :
    positiveLeafProbability tree reference / negativeLeafProbability tree reference =
      (((q - (discovered (negativeLeafQueries tree reference) reference).card).choose
        ((q - 1) / 2 + 1) : ℝ) / (q.choose ((q - 1) / 2 + 1) : ℝ)) := by
  rw [negativeLeafProbability_eq, positiveLeafProbability_eq]
  exact observation_likelihood_ratio hq _ _

theorem cellTree_likelihood_lower {q : ℕ} {Output : Type*} (hq : 5 ≤ q)
    (tree : CellTree q Output) (reference : Fin q → Fin q)
    (hdiscover : 4 * (discovered (negativeLeafQueries tree reference) reference).card ≤ q) :
    (1 : ℝ) / 5 ^ (discovered (negativeLeafQueries tree reference) reference).card ≤
      positiveLeafProbability tree reference / negativeLeafProbability tree reference := by
  rw [negativeLeafProbability_eq, positiveLeafProbability_eq]
  exact observation_likelihood_lower hq _ _ hdiscover

theorem negativeLeafQueries_card_le_depth {q : ℕ} {Output : Type*}
    (tree : CellTree q Output) (reference : Fin q → Fin q) :
    (negativeLeafQueries tree reference).card ≤ tree.depth :=
  OracleTree.queried_card_le_depth tree _

end QueryComplexity.PointerDistributions
