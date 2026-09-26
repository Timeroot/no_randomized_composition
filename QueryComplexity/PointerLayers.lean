import QueryComplexity.PointerMixture

namespace QueryComplexity.PointerDistributions

open scoped BigOperators
open FiniteProbability

abbrev BlockInput (q : ℕ) := Fin q → PointerInput q

noncomputable def productPrior (q : ℕ) : BlockInput q → ℝ :=
  ProductPosteriors.jointWeight (fun _ => mixedWeight q)

noncomputable def labelCount {q : ℕ} (x : BlockInput q) : ℕ :=
  (BoolCounting.trueSet (fun i => Pointer.value (x i))).card

noncomputable def layerWeight (q k : ℕ) (x : BlockInput q) : ℝ :=
  (if labelCount x = k then productPrior q x else 0) /
    BernoulliSmoothing.fairBinomialMass q k

theorem productPrior_nonnegative (q : ℕ) : Nonnegative (productPrior q) :=
  ProductPosteriors.jointWeight_nonnegative _ (fun _ => mixedWeight_nonnegative q)

theorem productPrior_mass (q : ℕ) (hq : 0 < q) : mass (productPrior q) = 1 := by
  rw [productPrior, ProductPosteriors.jointWeight_mass]
  simp [mixedWeight_mass q hq]

theorem productPrior_count_mass (q : ℕ) (hq : 0 < q) (k : ℕ) :
    (∑ x : BlockInput q, if labelCount x = k then productPrior q x else 0) =
      BernoulliSmoothing.fairBinomialMass q k := by
  have h := ProductPosteriors.joint_count_factor
    (fun _ : Fin q => mixedWeight q) (fun _ => Pointer.value)
    (fun _ => by rw [mixedWeight_mass q hq]; norm_num) (k : ℤ)
  have hp : ProductPosteriors.posterior (fun _ : Fin q => mixedWeight q)
      (fun _ => Pointer.value) = (fun _ => (1 : ℝ) / 2) :=
    funext (mixed_posterior q hq)
  rw [hp, BernoulliMixture.countMass_half] at h
  simpa [mixedWeight_mass q hq, BernoulliSmoothing.fairBinomialMassInt,
    labelCount, productPrior] using h

theorem fairBinomialMass_pos (q k : ℕ) (hk : k ≤ q) :
    0 < BernoulliSmoothing.fairBinomialMass q k := by
  unfold BernoulliSmoothing.fairBinomialMass
  exact div_pos (by exact_mod_cast Nat.choose_pos hk) (by positivity)

theorem layerWeight_nonnegative (q k : ℕ) : Nonnegative (layerWeight q k) := by
  intro x
  unfold layerWeight
  apply div_nonneg
  · split_ifs
    · exact productPrior_nonnegative q x
    · exact le_refl 0
  · unfold BernoulliSmoothing.fairBinomialMass
    positivity

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
  have hcount : labelCount x = m := by
    by_contra h
    exact hx (layerWeight_support x h)
  cases hlabel : cellMajority (2 * m + 1) x
  · rfl
  · have := (cellMajority_eq_true_iff _ x).1 hlabel
    omega

theorem upper_layer_label (m : ℕ) (x : BlockInput (2 * m + 1))
    (hx : layerWeight (2 * m + 1) (m + 1) x ≠ 0) : cellMajority (2 * m + 1) x = true := by
  have hcount : labelCount x = m + 1 := by
    by_contra h
    exact hx (layerWeight_support x h)
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
  change (mass (layerWeight (2 * m + 1) m) + mass (layerWeight (2 * m + 1) (m + 1))) / 2 = 1
  rw [layerWeight_mass _ _ (by omega) (by omega), layerWeight_mass _ _ (by omega) (by omega)]
  norm_num

end QueryComplexity.PointerDistributions
