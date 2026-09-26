import QueryComplexity.FiniteProbability
import QueryComplexity.BernoulliMixture

namespace QueryComplexity.ProductPosteriors

open scoped BigOperators
open FiniteProbability

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

noncomputable def jointWeight (ν : I → X → ℝ) (x : I → X) : ℝ := ∏ i, ν i (x i)

theorem jointWeight_mass (ν : I → X → ℝ) :
    mass (jointWeight ν) = ∏ i, mass (ν i) := by
  exact (Fintype.prod_sum ν).symm

theorem jointWeight_nonnegative (ν : I → X → ℝ) (hν : ∀ i x, 0 ≤ ν i x) :
    ∀ x, 0 ≤ jointWeight ν x := fun x => Finset.prod_nonneg (fun i _ => hν i (x i))

theorem joint_label_pushforward (ν : I → X → ℝ) (label : I → X → Bool) (z : I → Bool) :
    pushforward (jointWeight ν) (fun x i => label i (x i)) z =
      ∏ i, labelMass (label i) (ν i) (z i) := by
  classical
  simp only [pushforward, labelMass, mass, restrict]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.prod_ite_zero]
  have heq : (fun i => label i (x i)) = z ↔ ∀ i, label i (x i) = z i := funext_iff
  simp only [heq, jointWeight]

noncomputable def posterior (ν : I → X → ℝ) (label : I → X → Bool) (i : I) : ℝ :=
  labelMass (label i) (ν i) true / mass (ν i)

theorem posterior_bounds (ν : I → X → ℝ) (label : I → X → Bool)
    (hν : ∀ i x, 0 ≤ ν i x) (hmass : ∀ i, 0 < mass (ν i)) :
    ∀ i, 0 ≤ posterior ν label i ∧ posterior ν label i ≤ 1 := by
  intro i
  constructor
  · exact div_nonneg (labelMass_nonnegative (label i) (hν i) true) (hmass i).le
  · apply (div_le_one (hmass i)).2
    exact labelMass_le_mass (label i) (hν i) true

theorem labelMass_factor (ν : I → X → ℝ) (label : I → X → Bool)
    (hmass : ∀ i, mass (ν i) ≠ 0) (i : I) (b : Bool) :
    labelMass (label i) (ν i) b = mass (ν i) *
      (if b then posterior ν label i else 1 - posterior ν label i) := by
  have hsplit := labelMass_false_add_true (label i) (ν i)
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, posterior]
    field_simp [hmass i]
    nlinarith
  · simp only [↓reduceIte, posterior]
    field_simp [hmass i]

theorem joint_label_factor (ν : I → X → ℝ) (label : I → X → Bool)
    (hmass : ∀ i, mass (ν i) ≠ 0) (z : I → Bool) :
    (∏ i, labelMass (label i) (ν i) (z i)) =
      (∏ i, mass (ν i)) * BernoulliProduct.weight (posterior ν label) z := by
  simp_rw [labelMass_factor ν label hmass]
  exact Finset.prod_mul_distrib

/-- The conditional label count under a product of arbitrary nonnegative
local weights is the actual Poisson-binomial law used in the smoothing lemma. -/
theorem joint_count_factor (ν : I → X → ℝ) (label : I → X → Bool)
    (hmass : ∀ i, mass (ν i) ≠ 0) (k : ℤ) :
    (∑ x : I → X, if ((BoolCounting.trueSet (fun i => label i (x i))).card : ℤ) = k then
      jointWeight ν x else 0) =
      (∏ i, mass (ν i)) * BernoulliMixture.countMass (posterior ν label) k := by
  classical
  have hpush := sum_pushforward_mul (jointWeight ν) (fun x i => label i (x i))
    (fun z : I → Bool => if ((BoolCounting.trueSet z).card : ℤ) = k then (1 : ℝ) else 0)
  calc
    _ = ∑ z : I → Bool, if ((BoolCounting.trueSet z).card : ℤ) = k then
        ∏ i, labelMass (label i) (ν i) (z i) else 0 := by
      simpa only [joint_label_pushforward, mul_ite, mul_one, mul_zero] using hpush.symm
    _ = _ := by
      simp only [joint_label_factor ν label hmass, BernoulliMixture.countMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      split_ifs <;> simp

theorem joint_count_conditional (ν : I → X → ℝ) (label : I → X → Bool)
    (hmass : ∀ i, 0 < mass (ν i)) (k : ℤ) :
    (∑ x : I → X, if ((BoolCounting.trueSet (fun i => label i (x i))).card : ℤ) = k then
      jointWeight ν x else 0) / mass (jointWeight ν) =
      BernoulliMixture.countMass (posterior ν label) k := by
  rw [joint_count_factor ν label (fun i => (hmass i).ne') k, jointWeight_mass]
  exact mul_div_cancel_left₀ _ (Finset.prod_pos (fun i _ => hmass i)).ne'

end QueryComplexity.ProductPosteriors
