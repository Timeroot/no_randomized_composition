import QueryComplexity.PointerDistributions
import QueryComplexity.ProductPosteriors

namespace QueryComplexity.PointerDistributions

open scoped BigOperators
open FiniteProbability

noncomputable def mixedWeight (q : ℕ) (x : PointerInput q) : ℝ :=
  (negativeWeight q x + positiveWeight q x) / 2

theorem mixedWeight_nonnegative (q : ℕ) : Nonnegative (mixedWeight q) := by
  intro x
  exact div_nonneg (add_nonneg (negativeWeight_nonnegative q x) (positiveWeight_nonnegative q x))
    (by norm_num)

theorem mixedWeight_mass (q : ℕ) (hq : 0 < q) : mass (mixedWeight q) = 1 := by
  simp only [mass, mixedWeight, ← Finset.sum_div, Finset.sum_add_distrib]
  change (mass (negativeWeight q) + mass (positiveWeight q)) / 2 = 1
  rw [negativeWeight_mass, positiveWeight_mass q hq]
  norm_num

theorem negative_labelMass (q : ℕ) (b : Bool) :
    labelMass Pointer.value (negativeWeight q) b = if b then 0 else 1 := by
  cases b
  · have heq : restrict (negativeWeight q) Pointer.value false = negativeWeight q := by
      funext x
      cases hx : Pointer.value x
      · simp [restrict, hx]
      · simp [restrict, hx, negativeWeight_support x hx]
    change mass (restrict (negativeWeight q) Pointer.value false) = 1
    rw [heq, negativeWeight_mass]
  · apply Finset.sum_eq_zero
    intro x _
    cases hx : Pointer.value x
    · simp [restrict, hx]
    · simp [restrict, hx, negativeWeight_support x hx]

theorem positive_labelMass (q : ℕ) (hq : 0 < q) (b : Bool) :
    labelMass Pointer.value (positiveWeight q) b = if b then 1 else 0 := by
  cases b
  · apply Finset.sum_eq_zero
    intro x _
    cases hx : Pointer.value x
    · simp [restrict, hx, positiveWeight_support x hx]
    · simp [restrict, hx]
  · have heq : restrict (positiveWeight q) Pointer.value true = positiveWeight q := by
      funext x
      cases hx : Pointer.value x
      · simp [restrict, hx, positiveWeight_support x hx]
      · simp [restrict, hx]
    change mass (restrict (positiveWeight q) Pointer.value true) = 1
    rw [heq, positiveWeight_mass q hq]

theorem mixed_labelMass (q : ℕ) (hq : 0 < q) (b : Bool) :
    labelMass Pointer.value (mixedWeight q) b = (1 : ℝ) / 2 := by
  have heq : labelMass Pointer.value (mixedWeight q) b =
      (labelMass Pointer.value (negativeWeight q) b + labelMass Pointer.value (positiveWeight q) b) / 2 := by
    simp only [labelMass, mass, restrict, mixedWeight, ← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  rw [heq, negative_labelMass, positive_labelMass q hq]
  cases b <;> norm_num

theorem mixed_posterior (q : ℕ) (hq : 0 < q) {I : Type*} [Fintype I] [DecidableEq I] (i : I) :
    ProductPosteriors.posterior (fun _ : I => mixedWeight q) (fun _ => Pointer.value) i =
      (1 : ℝ) / 2 := by
  simp [ProductPosteriors.posterior, mixed_labelMass q hq, mixedWeight_mass q hq]

end QueryComplexity.PointerDistributions
