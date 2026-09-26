import QueryComplexity.PointerLayers

open scoped BigOperators

namespace QueryComplexity.PointerDistributions

open FiniteProbability

noncomputable def selectedWeight (q : ℕ) (b : Bool) : Weight (PointerInput q) :=
  if b then positiveWeight q else negativeWeight q

noncomputable def selectedProduct (q : ℕ) (z : Fin q → Bool) : Weight (BlockInput q) :=
  ProductPosteriors.jointWeight (fun i => selectedWeight q (z i))

noncomputable def layerLabelWeight (q k : ℕ) (z : Fin q → Bool) : ℝ :=
  (if (BoolCounting.trueSet z).card = k then (1 : ℝ) / 2 ^ q else 0) /
    BernoulliSmoothing.fairBinomialMass q k

theorem selectedWeight_eq (q : ℕ) (b : Bool) (x : PointerInput q) :
    selectedWeight q b x = if Pointer.value x = b then 2 * mixedWeight q x else 0 := by
  cases b <;> cases hx : Pointer.value x
  · simp [selectedWeight, mixedWeight, hx, positiveWeight_support x hx]
    ring
  · simp [selectedWeight, mixedWeight, hx, negativeWeight_support x hx]
  · simp [selectedWeight, mixedWeight, hx, positiveWeight_support x hx]
  · simp [selectedWeight, mixedWeight, hx, negativeWeight_support x hx]
    ring

theorem selectedProduct_eq (q : ℕ) (z : Fin q → Bool) (x : BlockInput q) :
    selectedProduct q z x =
      if (fun i => Pointer.value (x i)) = z then (2 : ℝ) ^ q * productPrior q x else 0 := by
  simp only [selectedProduct, ProductPosteriors.jointWeight, selectedWeight_eq,
    Fintype.prod_ite_zero, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, productPrior]
  simp only [funext_iff]

theorem selectedProduct_nonnegative (q : ℕ) (z : Fin q → Bool) :
    Nonnegative (selectedProduct q z) := by
  apply ProductPosteriors.jointWeight_nonnegative
  intro i x
  unfold selectedWeight
  split_ifs <;> first | exact positiveWeight_nonnegative q x | exact negativeWeight_nonnegative q x

theorem selectedProduct_mass (q : ℕ) (hq : 0 < q) (z : Fin q → Bool) :
    mass (selectedProduct q z) = 1 := by
  rw [selectedProduct, ProductPosteriors.jointWeight_mass]
  apply Finset.prod_eq_one
  intro i _
  unfold selectedWeight
  split_ifs <;> first | exact positiveWeight_mass q hq | exact negativeWeight_mass q

theorem layerLabelWeight_nonnegative (q k : ℕ) : Nonnegative (layerLabelWeight q k) := by
  intro z
  unfold layerLabelWeight BernoulliSmoothing.fairBinomialMass
  split_ifs <;> positivity

theorem layerLabelWeight_mass (q k : ℕ) (hk : k ≤ q) : mass (layerLabelWeight q k) = 1 := by
  simp only [mass, layerLabelWeight, ← Finset.sum_div]
  have hc := BoolCounting.fair_count_mass (I := Fin q) k
  simp only [Fintype.card_fin] at hc
  rw [hc]
  exact div_self (fairBinomialMass_pos q k hk).ne'

/-- A count-conditioned product prior is a convex mixture of independent
source distributions with a fixed complete label vector. -/
theorem layerWeight_mixture (q k : ℕ) (x : BlockInput q) :
    layerWeight q k x = ∑ z : Fin q → Bool, layerLabelWeight q k z * selectedProduct q z x := by
  classical
  rw [Finset.sum_eq_single (fun i => Pointer.value (x i))]
  · rw [selectedProduct_eq, if_pos rfl]
    unfold layerWeight layerLabelWeight labelCount
    split_ifs
    · field_simp
      <;> ring
    · simp only [zero_div, zero_mul]
  · intro z _ hz
    rw [selectedProduct_eq, if_neg (Ne.symm hz), mul_zero]
  · simp

theorem layerWeight_expectation (q k : ℕ) (φ : BlockInput q → ℝ) :
    (∑ x, layerWeight q k x * φ x) =
      ∑ z : Fin q → Bool, layerLabelWeight q k z * (∑ x, selectedProduct q z x * φ x) := by
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
  calc
    _ ≤ ∑ z : Fin q → Bool, layerLabelWeight q k z * M := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hz : (BoolCounting.trueSet z).card = k
      · exact mul_le_mul_of_nonneg_left (h z hz) (layerLabelWeight_nonnegative q k z)
      · simp only [layerLabelWeight, hz, if_false, zero_div, zero_mul, le_refl]
    _ = M := by
      rw [← Finset.sum_mul]
      change mass (layerLabelWeight q k) * M = M
      rw [layerLabelWeight_mass q k hk, one_mul]

end QueryComplexity.PointerDistributions
