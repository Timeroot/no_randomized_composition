import ForMathlib.Probability.FiniteProbability
import ForMathlib.Probability.BernoulliMixture

/-! Finite product distributions, label posteriors, and source averaging. -/

section

namespace ProductPosteriors

open scoped BigOperators
open FiniteProbability

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

noncomputable def jointWeight (ν : I → X → ℝ) (x : I → X) : ℝ := ∏ i, ν i (x i)

theorem jointWeight_mass (ν : I → X → ℝ) :
    mass (jointWeight ν) = ∏ i, mass (ν i) := by
  exact (Fintype.prod_sum ν).symm

omit [DecidableEq I] [Fintype X] in
theorem jointWeight_nonnegative (ν : I → X → ℝ) (hν : ∀ i x, 0 ≤ ν i x) :
    ∀ x, 0 ≤ jointWeight ν x := fun x => Finset.prod_nonneg (fun i _ => hν i (x i))

theorem joint_label_pushforward (ν : I → X → ℝ) (label : I → X → Bool) (z : I → Bool) :
    pushforward (jointWeight ν) (fun x i => label i (x i)) z =
      ∏ i, labelMass (label i) (ν i) (z i) := by
  classical
  simp only [pushforward, labelMass, mass, restrict]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.prod_ite_zero]
  have heq : (fun i => label i (x i)) = z ↔ ∀ i, label i (x i) = z i := funext_iff
  simp only [heq, jointWeight]

noncomputable def posterior (ν : I → X → ℝ) (label : I → X → Bool) (i : I) : ℝ :=
  labelMass (label i) (ν i) true / mass (ν i)

omit [Fintype I] [DecidableEq I] in
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

omit [DecidableEq I] in
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
      refine Finset.sum_congr rfl fun z _ => ?_
      split_ifs <;> simp

end ProductPosteriors

end

section

open scoped BigOperators

namespace ProductPosteriors

open FiniteProbability

variable {I X Y P H : Type*} [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y]
  [Fintype P] [Fintype H]

omit [Fintype Y] in
theorem joint_pushforward (ν : I → X → ℝ) (g : I → X → Y) (y : I → Y) :
    pushforward (jointWeight ν) (fun x i => g i (x i)) y =
      jointWeight (fun i => pushforward (ν i) (g i)) y := by
  classical
  simp only [pushforward, jointWeight]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.prod_ite_zero]
  simp only [funext_iff]

theorem joint_pushforward_expectation (ν : I → X → ℝ) (g : I → X → Y)
    (φ : (I → Y) → ℝ) :
    (∑ y, jointWeight (fun i => pushforward (ν i) (g i)) y * φ y) =
      ∑ x, jointWeight ν x * φ (fun i => g i (x i)) := by
  simp_rw [← joint_pushforward]
  exact sum_pushforward_mul _ _ _

def sourceSplit : (I → P × H) ≃ (I → P) × (I → H) where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun x := fun i => (x.1 i, x.2 i)
  left_inv x := by funext i; rfl
  right_inv x := by cases x; rfl

theorem uniform_joint (h : I → H) :
    jointWeight (fun _ => uniformWeight H) h = uniformWeight (I → H) h := by
  simp [jointWeight, uniformWeight, Nat.cast_pow]

theorem product_source_expectation (ν : P → ℝ) (φ : (I → P) → (I → H) → ℝ) :
    (∑ x : I → P × H, jointWeight (fun _ pair => ν pair.1 * uniformWeight H pair.2) x *
      φ (fun i => (x i).1) (fun i => (x i).2)) =
      ∑ p : I → P, jointWeight (fun _ => ν) p * average (fun h : I → H => φ p h) := by
  have he := (sourceSplit (I := I) (P := P) (H := H)).sum_comp
    (fun x : (I → P) × (I → H) => jointWeight (fun _ => ν) x.1 *
      uniformWeight (I → H) x.2 * φ x.1 x.2)
  simp only [sourceSplit, Equiv.coe_fn_mk] at he
  calc
    _ = ∑ x : I → P × H, jointWeight (fun _ => ν) (fun i => (x i).1) *
        uniformWeight (I → H) (fun i => (x i).2) * φ (fun i => (x i).1) (fun i => (x i).2) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← uniform_joint]
      simp only [jointWeight, Finset.prod_mul_distrib]
    _ = _ := by
      rw [he, Fintype.sum_prod_type]
      simp only [average, Finset.mul_sum, mul_assoc]

end ProductPosteriors

end
