import QueryComplexity.PointerLayers
import QueryComplexity.PointerVariance
import QueryComplexity.PosteriorLayers

open scoped BigOperators

namespace QueryComplexity

namespace OracleTree

variable {Coordinate Answer Output : Type*}

def leafOutput : (tree : OracleTree Coordinate Answer Output) → tree.Leaf → Output
  | .leaf output, _ => output
  | .query _ next, path => (next path.1).leafOutput path.2

@[simp] theorem leafOutput_route (tree : OracleTree Coordinate Answer Output)
    (x : Coordinate → Answer) : tree.leafOutput (tree.route x) = tree.eval x := by
  induction tree with
  | leaf output => rfl
  | query coordinate next ih => exact ih _

end OracleTree

namespace OraclePosteriors

open FiniteProbability ProductPosteriors

attribute [local instance] Classical.propDecidable

variable {I Coordinate Answer X Output : Type*}
  [Fintype I] [DecidableEq I] [Fintype X]

/-- Product factorization also holds at zero-mass leaves. -/
theorem leaf_count_factor_nonnegative (ν : I → X → ℝ) (hν : ∀ i x, 0 ≤ ν i x)
    (read : X → Coordinate → Answer) (label : I → X → Bool)
    (tree : OracleTree (I × Coordinate) Answer Output) (leaf : tree.Leaf) (k : ℤ) :
    (∑ x : I → X, if ((BoolCounting.trueSet (fun i => label i (x i))).card : ℤ) = k then
      (if tree.route (fun coordinate => read (x coordinate.1) coordinate.2) = leaf then
        jointWeight ν x else 0) else 0) =
      leafMass ν read tree leaf *
        BernoulliMixture.countMass (posterior (localWeight ν read (tree.transcript leaf)) label) k := by
  classical
  by_cases hn : ∀ i, mass (localWeight ν read (tree.transcript leaf) i) ≠ 0
  · exact leaf_count_factor ν read label tree leaf hn k
  · push_neg at hn
    obtain ⟨i, hi⟩ := hn
    have hw (j : I) (x : X) : 0 ≤ localWeight ν read (tree.transcript leaf) j x := by
      unfold localWeight
      split_ifs
      · exact hν j x
      · exact le_rfl
    have hz (x : X) : localWeight ν read (tree.transcript leaf) i x = 0 := by
      apply le_antisymm _ (hw i x)
      have h := Finset.single_le_sum (fun a (_ : a ∈ (Finset.univ : Finset X)) => hw i a)
        (Finset.mem_univ x)
      exact h.trans_eq hi
    have hprod (x : I → X) : jointWeight (localWeight ν read (tree.transcript leaf)) x = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (hz (x i))
    have hleaf : leafMass ν read tree leaf = 0 := by
      rw [leafMass_product]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    simp_rw [← leaf_weight_factor ν read tree leaf, hprod]
    simp [hleaf]

end OraclePosteriors

namespace PointerDistributions

open FiniteProbability

variable {q : ℕ} {Output : Type*}

noncomputable def leafPrior
    (tree : OracleTree (Fin q × (Fin q × Fin q)) (PointerCell q) Output) : tree.Leaf → ℝ :=
  OraclePosteriors.leafMass (fun _ => mixedWeight q) cellInput tree

noncomputable def leafPosterior
    (tree : OracleTree (Fin q × (Fin q × Fin q)) (PointerCell q) Output)
    (leaf : tree.Leaf) : Fin q → ℝ := localPosterior (tree.transcript leaf)

theorem leafPrior_nonnegative
    (tree : OracleTree (Fin q × (Fin q × Fin q)) (PointerCell q) Output) : Nonnegative (leafPrior tree) :=
  OraclePosteriors.leafMass_nonnegative _ (fun _ => mixedWeight_nonnegative q) _ _

theorem leafPrior_mass (hq : 0 < q)
    (tree : OracleTree (Fin q × (Fin q × Fin q)) (PointerCell q) Output) : mass (leafPrior tree) = 1 := by
  unfold leafPrior mass
  rw [OraclePosteriors.leafMass_sum]
  exact productPrior_mass q hq

theorem leafPosterior_bounds
    (tree : OracleTree (Fin q × (Fin q × Fin q)) (PointerCell q) Output) (leaf : tree.Leaf) (i : Fin q) :
    0 ≤ leafPosterior tree leaf i ∧ leafPosterior tree leaf i ≤ 1 :=
  localPosterior_bounds _ _

noncomputable def layerLeafWeight
    (tree : OracleTree (Fin q × (Fin q × Fin q)) (PointerCell q) Output) (k : ℕ) : tree.Leaf → ℝ :=
  pushforward (layerWeight q k) (fun x => tree.route (fun coordinate => cellInput (x coordinate.1) coordinate.2))

theorem layerLeafWeight_eq_conditioned
    (tree : OracleTree (Fin q × (Fin q × Fin q)) (PointerCell q) Output) (k : ℕ) (leaf : tree.Leaf) :
    layerLeafWeight tree k leaf =
      PosteriorMajority.conditionedCountWeight (leafPrior tree) (leafPosterior tree)
        (BernoulliSmoothing.fairBinomialMass q k) (k : ℤ) leaf := by
  classical
  have hfactor := OraclePosteriors.leaf_count_factor_nonnegative
    (fun _ : Fin q => mixedWeight q) (fun _ => mixedWeight_nonnegative q)
    cellInput (fun _ => Pointer.value) tree leaf (k : ℤ)
  have hnum : layerLeafWeight tree k leaf =
      (∑ x : BlockInput q, if labelCount x = k then
        (if tree.route (fun coordinate => cellInput (x coordinate.1) coordinate.2) = leaf then
          productPrior q x else 0) else 0) / BernoulliSmoothing.fairBinomialMass q k := by
    unfold layerLeafWeight pushforward layerWeight
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  rw [hnum]
  unfold PosteriorMajority.conditionedCountWeight
  congr 1
  simpa only [Nat.cast_inj, labelCount, productPrior, leafPrior, leafPosterior, localPosterior] using hfactor

theorem layerLeafWeight_nonnegative
    (tree : OracleTree (Fin q × (Fin q × Fin q)) (PointerCell q) Output) (k : ℕ) :
    Nonnegative (layerLeafWeight tree k) :=
  pushforward_nonnegative (layerWeight_nonnegative q k) _

theorem layerLeafWeight_mass (hq : 0 < q)
    (tree : OracleTree (Fin q × (Fin q × Fin q)) (PointerCell q) Output) (k : ℕ) (hk : k ≤ q) :
    mass (layerLeafWeight tree k) = 1 := by
  rw [layerLeafWeight, mass_pushforward]
  exact layerWeight_mass q k hq hk

theorem layerLeafWeight_event
    (tree : OracleTree (Fin q × (Fin q × Fin q)) (PointerCell q) Output) (k : ℕ)
    (event : tree.Leaf → Prop) [DecidablePred event] :
    (∑ leaf, if event leaf then layerLeafWeight tree k leaf else 0) =
      ∑ x : BlockInput q,
        if event (tree.route (fun coordinate => cellInput (x coordinate.1) coordinate.2))
        then layerWeight q k x else 0 := by
  have h := sum_pushforward_mul (layerWeight q k)
    (fun x => tree.route (fun coordinate => cellInput (x coordinate.1) coordinate.2))
    (fun leaf => if event leaf then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero] using h

theorem odd_middle_prior_eq (m : ℕ) :
    BernoulliSmoothing.fairBinomialMass (2 * m + 1) (m + 1) =
      BernoulliSmoothing.fairBinomialMass (2 * m + 1) m := by
  unfold BernoulliSmoothing.fairBinomialMass
  congr 2
  have h := Nat.choose_symm (show m ≤ 2 * m + 1 by omega)
  simpa only [show 2 * m + 1 - m = m + 1 by omega] using h

/-- Exact success accounting for the adjacent-layer hard distribution. -/
theorem majority_tree_success_eq (m : ℕ)
    (tree : OracleTree (Fin (2 * m + 1) × (Fin (2 * m + 1) × Fin (2 * m + 1)))
      (PointerCell (2 * m + 1)) Bool) :
    (∑ x : BlockInput (2 * m + 1),
      if tree.eval (fun coordinate => cellInput (x coordinate.1) coordinate.2) = cellMajority (2 * m + 1) x
      then majorityHardWeight m x else 0) =
      (1 : ℝ) / 2 * ∑ leaf, if tree.leafOutput leaf then layerLeafWeight tree (m + 1) leaf
        else layerLeafWeight tree m leaf := by
  classical
  have hpoint (x : BlockInput (2 * m + 1)) :
      (if tree.eval (fun coordinate => cellInput (x coordinate.1) coordinate.2) = cellMajority (2 * m + 1) x
        then majorityHardWeight m x else 0) =
      (layerWeight (2 * m + 1) m x *
        (if tree.eval (fun coordinate => cellInput (x coordinate.1) coordinate.2) = false then 1 else 0) +
       layerWeight (2 * m + 1) (m + 1) x *
        (if tree.eval (fun coordinate => cellInput (x coordinate.1) coordinate.2) = true then 1 else 0)) / 2 := by
    have hlo : layerWeight (2 * m + 1) m x = 0 ∨ cellMajority (2 * m + 1) x = false := by
      by_cases h : layerWeight (2 * m + 1) m x = 0
      · exact Or.inl h
      · exact Or.inr (lower_layer_label m x h)
    have hhi : layerWeight (2 * m + 1) (m + 1) x = 0 ∨ cellMajority (2 * m + 1) x = true := by
      by_cases h : layerWeight (2 * m + 1) (m + 1) x = 0
      · exact Or.inl h
      · exact Or.inr (upper_layer_label m x h)
    cases hout : tree.eval (fun coordinate => cellInput (x coordinate.1) coordinate.2) <;>
      cases hlabel : cellMajority (2 * m + 1) x <;>
      simp_all [majorityHardWeight]
  simp_rw [hpoint]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have hpush (k : ℕ) (b : Bool) :
      (∑ x : BlockInput (2 * m + 1), layerWeight (2 * m + 1) k x *
        (if tree.eval (fun coordinate => cellInput (x coordinate.1) coordinate.2) = b then 1 else 0)) =
      ∑ leaf, layerLeafWeight tree k leaf * (if tree.leafOutput leaf = b then 1 else 0) := by
    symm
    exact (sum_pushforward_mul (layerWeight (2 * m + 1) k)
      (fun x => tree.route (fun coordinate => cellInput (x coordinate.1) coordinate.2))
      (fun leaf => if tree.leafOutput leaf = b then 1 else 0)).trans (by simp)
  rw [hpush, hpush, ← Finset.sum_add_distrib]
  rw [show (1 : ℝ) / 2 * (∑ leaf, if tree.leafOutput leaf then layerLeafWeight tree (m + 1) leaf
      else layerLeafWeight tree m leaf) =
      (∑ leaf, if tree.leafOutput leaf then layerLeafWeight tree (m + 1) leaf
      else layerLeafWeight tree m leaf) / 2 by ring]
  congr 1
  apply Finset.sum_congr rfl
  intro leaf _
  cases tree.leafOutput leaf <;> simp

/-- Apply adjacent-layer smoothing directly to the actual query-tree score.
The remaining hypotheses are probabilities of the low-variance event under
the two actual source layers. -/
theorem majority_tree_success_le_layers (m : ℕ)
    (tree : OracleTree (Fin (2 * m + 1) × (Fin (2 * m + 1) × Fin (2 * m + 1)))
      (PointerCell (2 * m + 1)) Bool)
    (v δ₀ δ₁ : ℝ) (hv : 0 < v)
    (hbad₀ : (∑ leaf, if v ≤ PosteriorMajority.variance (leafPosterior tree leaf)
      then 0 else layerLeafWeight tree m leaf) ≤ δ₀)
    (hbad₁ : (∑ leaf, if v ≤ PosteriorMajority.variance (leafPosterior tree leaf)
      then 0 else layerLeafWeight tree (m + 1) leaf) ≤ δ₁) :
    (∑ x : BlockInput (2 * m + 1),
      if tree.eval (fun coordinate => cellInput (x coordinate.1) coordinate.2) = cellMajority (2 * m + 1) x
      then majorityHardWeight m x else 0) ≤
      1 / 2 + 1 / 4 * (1 / (v * BernoulliSmoothing.fairBinomialMass (2 * m + 1) m) + δ₀ + δ₁) := by
  classical
  let prior := BernoulliSmoothing.fairBinomialMass (2 * m + 1) m
  have hlower (leaf : tree.Leaf) : layerLeafWeight tree m leaf =
      PosteriorMajority.conditionedCountWeight (leafPrior tree) (leafPosterior tree) prior (m : ℤ) leaf :=
    layerLeafWeight_eq_conditioned tree m leaf
  have hupper (leaf : tree.Leaf) : layerLeafWeight tree (m + 1) leaf =
      PosteriorMajority.conditionedCountWeight (leafPrior tree) (leafPosterior tree) prior ((m : ℤ) + 1) leaf := by
    rw [layerLeafWeight_eq_conditioned, odd_middle_prior_eq]
    simp only [Nat.cast_add, Nat.cast_one, prior]
  have h := PosteriorMajority.binary_success_le_layers (leafPrior tree)
    (leafPrior_nonnegative tree) (leafPrior_mass (by omega) tree) (leafPosterior tree)
    (leafPosterior_bounds tree)
    (fun leaf => v ≤ PosteriorMajority.variance (leafPosterior tree leaf))
    v δ₀ δ₁ prior hv (fairBinomialMass_pos _ _ (by omega))
    (fun _ _ h => h) (m : ℤ)
    (by simpa only [hlower] using hbad₀)
    (by simpa only [hupper] using hbad₁)
    (by simpa only [mass, hlower] using layerLeafWeight_mass (by omega) tree m (by omega))
    (by simpa only [mass, hupper] using layerLeafWeight_mass (by omega) tree (m + 1) (by omega))
    tree.leafOutput
  rw [majority_tree_success_eq]
  simpa only [← hlower, ← hupper] using h

end PointerDistributions

end QueryComplexity
