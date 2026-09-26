import QueryComplexity.OracleTrees
import QueryComplexity.ProductPosteriors

namespace QueryComplexity.OraclePosteriors

open scoped BigOperators
open FiniteProbability ProductPosteriors

variable {I Coordinate Answer X Output : Type*}
variable [Fintype I] [DecidableEq I] [Fintype X]

attribute [local instance] Classical.propDecidable

def localMatches (read : X → Coordinate → Answer)
    (trace : List ((I × Coordinate) × Answer)) (i : I) (x : X) : Prop :=
  ∀ entry ∈ trace, entry.1.1 = i → read x entry.1.2 = entry.2

noncomputable def localWeight (ν : I → X → ℝ) (read : X → Coordinate → Answer)
    (trace : List ((I × Coordinate) × Answer)) (i : I) (x : X) : ℝ := by
  classical
  exact if localMatches read trace i x then ν i x else 0

theorem matches_iff_local (read : X → Coordinate → Answer)
    (trace : List ((I × Coordinate) × Answer)) (x : I → X) :
    OracleTree.Matches trace (fun coordinate => read (x coordinate.1) coordinate.2) ↔
      ∀ i, localMatches read trace i (x i) := by
  constructor
  · intro h i entry hentry hi
    have heq := h entry hentry
    simpa [hi] using heq
  · intro h entry hentry
    exact h entry.1.1 entry hentry rfl

/-- A full adaptive leaf restricts the product prior by one local condition
per block, so its unnormalized posterior remains a product. -/
theorem leaf_weight_factor (ν : I → X → ℝ) (read : X → Coordinate → Answer)
    (tree : OracleTree (I × Coordinate) Answer Output) (leaf : tree.Leaf) (x : I → X) :
    jointWeight (localWeight ν read (tree.transcript leaf)) x =
      if tree.route (fun coordinate => read (x coordinate.1) coordinate.2) = leaf then
        jointWeight ν x else 0 := by
  classical
  simp only [jointWeight, localWeight, Fintype.prod_ite_zero]
  have hiff := (OracleTree.route_eq_iff tree leaf
    (fun coordinate => read (x coordinate.1) coordinate.2)).trans
      (matches_iff_local read (tree.transcript leaf) x)
  simp only [hiff]

noncomputable def leafMass (ν : I → X → ℝ) (read : X → Coordinate → Answer)
    (tree : OracleTree (I × Coordinate) Answer Output) (leaf : tree.Leaf) : ℝ :=
  ∑ x : I → X, if tree.route (fun coordinate => read (x coordinate.1) coordinate.2) = leaf then
    jointWeight ν x else 0

theorem leafMass_product (ν : I → X → ℝ) (read : X → Coordinate → Answer)
    (tree : OracleTree (I × Coordinate) Answer Output) (leaf : tree.Leaf) :
    leafMass ν read tree leaf = ∏ i, mass (localWeight ν read (tree.transcript leaf) i) := by
  unfold leafMass
  simp_rw [← leaf_weight_factor ν read tree leaf]
  exact jointWeight_mass _

theorem leafMass_nonnegative (ν : I → X → ℝ) (hν : ∀ i x, 0 ≤ ν i x)
    (read : X → Coordinate → Answer)
    (tree : OracleTree (I × Coordinate) Answer Output) (leaf : tree.Leaf) :
    0 ≤ leafMass ν read tree leaf := by
  classical
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact jointWeight_nonnegative ν hν x
  · exact le_refl 0

theorem leafMass_sum [Fintype Answer] (ν : I → X → ℝ) (read : X → Coordinate → Answer)
    (tree : OracleTree (I × Coordinate) Answer Output) :
    (∑ leaf, leafMass ν read tree leaf) = mass (jointWeight ν) := by
  classical
  unfold leafMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

theorem leaf_count_factor (ν : I → X → ℝ) (read : X → Coordinate → Answer)
    (label : I → X → Bool) (tree : OracleTree (I × Coordinate) Answer Output) (leaf : tree.Leaf)
    (hmass : ∀ i, mass (localWeight ν read (tree.transcript leaf) i) ≠ 0) (k : ℤ) :
    (∑ x : I → X, if ((BoolCounting.trueSet (fun i => label i (x i))).card : ℤ) = k then
      (if tree.route (fun coordinate => read (x coordinate.1) coordinate.2) = leaf then
        jointWeight ν x else 0) else 0) =
      leafMass ν read tree leaf *
        BernoulliMixture.countMass (posterior (localWeight ν read (tree.transcript leaf)) label) k := by
  simp_rw [← leaf_weight_factor ν read tree leaf]
  rw [joint_count_factor _ label hmass k, leafMass_product]

end QueryComplexity.OraclePosteriors
