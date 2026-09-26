import QueryComplexity.PointerSourceAveraging
import QueryComplexity.PointerLeafLaws
import QueryComplexity.PointerLowerNumerics

namespace QueryComplexity.PointerDistributions

open scoped BigOperators
open FiniteProbability

attribute [local instance] Classical.propDecidable

theorem negativeBlocks_count (q k : ℕ) (z : Fin q → Bool)
    (hz : (BoolCounting.trueSet z).card = k) (hk : 2 * k ≤ q + 1) :
    q ≤ 2 * (Finset.univ.filter (fun i => z i = false)).card + 1 := by
  have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : Fin q => z i = true)
  have heq : (Finset.univ.filter (fun i : Fin q => ¬ z i = true)) =
      Finset.univ.filter (fun i => z i = false) := by
    ext i
    simp
  rw [heq, Finset.card_univ, Fintype.card_fin] at hsum
  have htrue : (Finset.univ.filter (fun i : Fin q => z i = true)).card = k := hz
  omega

/-- The exceptional posterior-variance event is small under either central
count layer; its probability is charged directly under that layer. -/
theorem layer_bad_variance_bound {q r : ℕ} {Output : Type*} (hq : 5 ≤ q) (hr : 0 < r)
    (hrsmall : 4 * r ≤ q) (tree : BlockCellTree q Output) (k : ℕ)
    (hk : k ≤ q) (hkcentral : 2 * k ≤ q + 1) :
    (∑ x : BlockInput q, layerWeight q k x *
      (if varianceGood tree ((q : ℝ) / (16 * (5 : ℝ) ^ r)) x then (0 : ℝ) else 1)) ≤
      (2 * tree.depth / q) / ((q : ℝ) * r / 8) := by
  apply layerWeight_expectation_le q k hk
  intro z hz
  apply selectedProduct_expectation_le q (by omega) z
  intro positives
  exact fixedLabel_bad_variance_bound hq hr hrsmall tree z
    (negativeBlocks_count q k z hz hkcentral) positives

theorem layer_bad_variance_le_one_fiftieth (s : ℕ) (hs : 1000 ≤ s) {Output : Type*}
    (tree : BlockCellTree (PointerLowerNumerics.arity s) Output)
    (hdepth : tree.depth ≤ PointerLowerNumerics.cellBudget s)
    (k : ℕ) (hk : k ≤ PointerLowerNumerics.arity s)
    (hkcentral : 2 * k ≤ PointerLowerNumerics.arity s + 1) :
    (∑ x : BlockInput (PointerLowerNumerics.arity s),
      layerWeight (PointerLowerNumerics.arity s) k x *
        (if varianceGood tree (PointerLowerNumerics.varianceBound s) x then (0 : ℝ) else 1)) ≤
      (1 : ℝ) / 50 := by
  have hq : 5 ≤ PointerLowerNumerics.arity s := by
    have h := Nat.lt_two_pow_self (n := s)
    unfold PointerLowerNumerics.arity
    omega
  have h := layer_bad_variance_bound hq (PointerLowerNumerics.cutoff_pos s hs)
    (PointerLowerNumerics.cutoff_le_arity s hs) tree k hk hkcentral
  apply h.trans
  apply le_trans _ (PointerLowerNumerics.discovery_markov_le s hs)
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hdepth) (by norm_num)

theorem layer_leaf_bad_variance_eq {q : ℕ} {Output : Type*}
    (tree : BlockCellTree q Output) (k : ℕ) (v : ℝ) :
    (∑ leaf, if v ≤ PosteriorMajority.variance (leafPosterior tree leaf)
      then 0 else layerLeafWeight tree k leaf) =
      ∑ x : BlockInput q, layerWeight q k x * (if varianceGood tree v x then (0 : ℝ) else 1) := by
  have h := layerLeafWeight_event tree k
    (fun leaf => ¬ v ≤ PosteriorMajority.variance (leafPosterior tree leaf))
  simpa only [ite_not, mul_ite, mul_zero, mul_one, varianceGood, leafPosterior] using h

/-- An explicit adjacent-layer distribution defeats every cell-query tree
below the stated budget. All adaptive and posterior estimates are internal. -/
theorem pointer_majority_cell_hard (s m : ℕ) (hs : 1000 ≤ s)
    (hq : PointerLowerNumerics.arity s = 2 * m + 1)
    (tree : BlockCellTree (2 * m + 1) Bool)
    (hdepth : tree.depth ≤ PointerLowerNumerics.cellBudget s) :
    (∑ x : BlockInput (2 * m + 1),
      if tree.eval (blockRead x) = cellMajority (2 * m + 1) x
        then majorityHardWeight m x else 0) ≤ (3 : ℝ) / 5 := by
  have hb (k : ℕ) (hk : k ≤ 2 * m + 1) (hkc : 2 * k ≤ (2 * m + 1) + 1) :
      (∑ leaf, if PointerLowerNumerics.varianceBound s ≤
        PosteriorMajority.variance (leafPosterior tree leaf)
        then 0 else layerLeafWeight tree k leaf) ≤ (1 : ℝ) / 50 := by
    rw [layer_leaf_bad_variance_eq]
    have h := @layer_bad_variance_le_one_fiftieth s hs Bool
    rw [hq] at h
    exact h tree hdepth k hk hkc
  have hscore := majority_tree_success_le_layers m tree (PointerLowerNumerics.varianceBound s)
    ((1 : ℝ) / 50) ((1 : ℝ) / 50) (PointerLowerNumerics.varianceBound_pos s hs)
    (hb m (by omega) (by omega)) (hb (m + 1) (by omega) (by omega))
  have hm : 1 ≤ m := by
    have h := PointerLowerNumerics.exponential_margin s hs
    have hpow : 0 < 25 ^ PointerLowerNumerics.cutoff s := by positivity
    omega
  have hπ := fairBinomialMass_pos (2 * m + 1) m (by omega)
  have hsquare := BernoulliSmoothing.fairBinomialMass_odd_square_lower m hm
  have hinv := PointerLowerNumerics.inverse_variance_prior_le s m hs hq
    (BernoulliSmoothing.fairBinomialMass (2 * m + 1) m) hπ.le hsquare
  change (∑ x : BlockInput (2 * m + 1),
    if tree.eval (fun coordinate => cellInput (x coordinate.1) coordinate.2) =
      cellMajority (2 * m + 1) x then majorityHardWeight m x else 0) ≤ (3 : ℝ) / 5
  linarith

end QueryComplexity.PointerDistributions
