import QueryComplexity.PointerFunction.Distributions

namespace QueryComplexity.PointerDistributions

open scoped BigOperators
open FiniteProbability BernoulliSmoothing

abbrev BlockInput (q : ℕ) := Fin q → PointerInput q

noncomputable def productPrior (q : ℕ) : BlockInput q → ℝ :=
  ProductPosteriors.jointWeight (fun _ => mixedWeight q)

noncomputable def labelCount {q : ℕ} (x : BlockInput q) : ℕ :=
  (BoolCounting.trueSet (fun i => Pointer.value (x i))).card

noncomputable def layerWeight (q k : ℕ) (x : BlockInput q) : ℝ :=
  (if labelCount x = k then productPrior q x else 0) /
    fairBinomialMass q k

theorem productPrior_nonnegative (q : ℕ) : Nonnegative (productPrior q) :=
  ProductPosteriors.jointWeight_nonnegative _ (fun _ => mixedWeight_nonnegative q)

theorem productPrior_mass (q : ℕ) (hq : 0 < q) : mass (productPrior q) = 1 := by
  rw [productPrior, ProductPosteriors.jointWeight_mass]
  simp [mixedWeight_mass q hq]

theorem productPrior_count_mass (q : ℕ) (hq : 0 < q) (k : ℕ) :
    (∑ x : BlockInput q, if labelCount x = k then productPrior q x else 0) =
      fairBinomialMass q k := by
  have h := ProductPosteriors.joint_count_factor
    (fun _ : Fin q => mixedWeight q) (fun _ => Pointer.value)
    (fun _ => by rw [mixedWeight_mass q hq]; norm_num) (k : ℤ)
  have hp : ProductPosteriors.posterior (fun _ : Fin q => mixedWeight q)
      (fun _ => Pointer.value) = (fun _ => (1 : ℝ) / 2) :=
    funext (mixed_posterior q hq)
  rw [hp, BernoulliMixture.countMass_half] at h
  simpa [mixedWeight_mass q hq, fairBinomialMassInt,
    labelCount, productPrior] using h

theorem layerWeight_nonnegative (q k : ℕ) : Nonnegative (layerWeight q k) := by
  intro x
  have hx := productPrior_nonnegative q x
  unfold layerWeight fairBinomialMass
  split_ifs <;> positivity

theorem layerWeight_mass (q k : ℕ) (hq : 0 < q) (hk : k ≤ q) :
    mass (layerWeight q k) = 1 := by
  simp only [mass, layerWeight, ← Finset.sum_div]
  rw [productPrior_count_mass q hq k]
  exact div_self (fairBinomialMass_pos q k hk).ne'

noncomputable def cellMajority (q : ℕ) (x : BlockInput q) : Bool :=
  Pointer.majority q (fun i => Pointer.value (x i))

theorem cellMajority_eq_true_iff (q : ℕ) (x : BlockInput q) :
    cellMajority q x = true ↔ q < 2 * labelCount x := by
  simp [cellMajority, Pointer.majority, labelCount, BoolCounting.trueSet]

theorem layerWeight_support {q k : ℕ} (x : BlockInput q) (hcount : labelCount x ≠ k) :
    layerWeight q k x = 0 := by simp [layerWeight, hcount]

theorem lower_layer_label (m : ℕ) (x : BlockInput (2 * m + 1))
    (hx : layerWeight (2 * m + 1) m x ≠ 0) : cellMajority (2 * m + 1) x = false := by
  have hcount : labelCount x = m := not_imp_comm.mp (layerWeight_support x) hx
  have := cellMajority_eq_true_iff (2 * m + 1) x
  grind

theorem upper_layer_label (m : ℕ) (x : BlockInput (2 * m + 1))
    (hx : layerWeight (2 * m + 1) (m + 1) x ≠ 0) : cellMajority (2 * m + 1) x = true := by
  have hcount : labelCount x = m + 1 := not_imp_comm.mp (layerWeight_support x) hx
  apply (cellMajority_eq_true_iff _ x).2
  omega

noncomputable def majorityHardWeight (m : ℕ) (x : BlockInput (2 * m + 1)) : ℝ :=
  (layerWeight (2 * m + 1) m x + layerWeight (2 * m + 1) (m + 1) x) / 2

theorem majorityHardWeight_nonnegative (m : ℕ) : Nonnegative (majorityHardWeight m) := by
  intro x
  exact div_nonneg (add_nonneg (layerWeight_nonnegative _ _ x) (layerWeight_nonnegative _ _ x))
    (by norm_num)

theorem majorityHardWeight_mass (m : ℕ) : mass (majorityHardWeight m) = 1 := by
  simp only [mass, majorityHardWeight, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [← mass, ← mass, layerWeight_mass _ _ (by omega) (by omega),
    layerWeight_mass _ _ (by omega) (by omega)]
  norm_num

end QueryComplexity.PointerDistributions

open scoped BigOperators

namespace QueryComplexity.PointerDistributions

open FiniteProbability BernoulliSmoothing

noncomputable def selectedWeight (q : ℕ) (b : Bool) : Weight (PointerInput q) :=
  if b then positiveWeight q else negativeWeight q

noncomputable def selectedProduct (q : ℕ) (z : Fin q → Bool) : Weight (BlockInput q) :=
  ProductPosteriors.jointWeight (fun i => selectedWeight q (z i))

theorem selectedWeight_eq (q : ℕ) (b : Bool) (x : PointerInput q) :
    selectedWeight q b x = if Pointer.value x = b then 2 * mixedWeight q x else 0 := by
  cases b <;> cases hx : Pointer.value x <;>
    simp [selectedWeight, mixedWeight, positiveWeight_support, negativeWeight_support, hx] <;> ring

theorem selectedProduct_eq (q : ℕ) (z : Fin q → Bool) (x : BlockInput q) :
    selectedProduct q z x =
      if (fun i => Pointer.value (x i)) = z then (2 : ℝ) ^ q * productPrior q x else 0 := by
  simp only [selectedProduct, ProductPosteriors.jointWeight, selectedWeight_eq,
    Fintype.prod_ite_zero, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, productPrior]
  simp only [funext_iff]

/-- A count-conditioned product prior is a convex mixture of independent
source distributions with a fixed complete label vector. -/
theorem layerWeight_mixture (q k : ℕ) (x : BlockInput q) :
    layerWeight q k x = ∑ z : Fin q → Bool, fairLayerWeight k z * selectedProduct q z x := by
  classical
  rw [Finset.sum_eq_single (fun i => Pointer.value (x i))]
  · rw [selectedProduct_eq, if_pos rfl]
    unfold layerWeight fairLayerWeight labelCount
    simp only [Fintype.card_fin]
    split_ifs
    · field_simp
    · simp only [zero_div, zero_mul]
  · intro z _ hz
    rw [selectedProduct_eq, if_neg (Ne.symm hz), mul_zero]
  · simp

theorem layerWeight_expectation (q k : ℕ) (φ : BlockInput q → ℝ) :
    (∑ x, layerWeight q k x * φ x) =
      ∑ z : Fin q → Bool, fairLayerWeight k z * (∑ x, selectedProduct q z x * φ x) := by
  simp only [layerWeight_mixture, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- Any uniform bound for each fixed label-vector source passes to the
normalized count layer, without requiring the bound to be nonnegative. -/
theorem layerWeight_expectation_le (q k : ℕ) (hk : k ≤ q)
    (φ : BlockInput q → ℝ) (M : ℝ)
    (h : ∀ z : Fin q → Bool, (BoolCounting.trueSet z).card = k →
      (∑ x, selectedProduct q z x * φ x) ≤ M) :
    (∑ x, layerWeight q k x * φ x) ≤ M := by
  rw [layerWeight_expectation]
  apply sum_mul_le_of_mass_one (fairLayerWeight_nonneg k)
    (sum_fairLayerWeight k (by simpa using hk))
  intro z hz
  apply h z
  by_contra hcount
  exact hz (by simp [fairLayerWeight, hcount])

end QueryComplexity.PointerDistributions
