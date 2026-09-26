import QueryComplexity.FiniteProbability
import QueryComplexity.FiniteResampling

open scoped BigOperators

namespace QueryComplexity.FiniteProbability

universe u v

noncomputable def average {X : Type u} [Fintype X] (f : X → ℝ) : ℝ :=
  ∑ x, uniformWeight X x * f x

theorem average_const {X : Type u} [Fintype X] [Nonempty X] (c : ℝ) :
    average (fun _ : X => c) = c := by
  unfold average
  rw [← Finset.sum_mul]
  change mass (uniformWeight X) * c = c
  rw [mass_uniformWeight, one_mul]

theorem average_le {X : Type u} [Fintype X] {f g : X → ℝ} (h : ∀ x, f x ≤ g x) :
    average f ≤ average g := Finset.sum_le_sum fun x _ =>
  mul_le_mul_of_nonneg_left (h x) (uniformWeight_nonnegative X x)

theorem average_add {X : Type u} [Fintype X] (f g : X → ℝ) :
    average (fun x => f x + g x) = average f + average g := by
  simp only [average, mul_add, Finset.sum_add_distrib]

theorem average_mul {X : Type u} [Fintype X] (c : ℝ) (f : X → ℝ) :
    average (fun x => c * f x) = c * average f := by
  simp only [average, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem average_div {X : Type u} [Fintype X] (f : X → ℝ) (c : ℝ) :
    average (fun x => f x / c) = average f / c := by
  simpa only [div_eq_mul_inv, mul_comm] using average_mul c⁻¹ f

theorem average_sum {X : Type u} {J : Type v} [Fintype X] [Fintype J]
    (f : J → X → ℝ) : average (fun x => ∑ j, f j x) = ∑ j, average (f j) := by
  simp only [average, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem average_equiv {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (f : Y → ℝ) : average (fun x => f (e x)) = average f := by
  simp only [average, uniformWeight, ← Finset.mul_sum]
  rw [Fintype.card_congr e, e.sum_comp]

theorem average_prod {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    (f : X × Y → ℝ) : average f = average (fun x => average (fun y => f (x, y))) := by
  simp only [average, uniformWeight, Fintype.sum_prod_type, Finset.mul_sum,
    Fintype.card_prod, Nat.cast_mul]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp only [mul_inv_rev]
  ring

theorem average_comm {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    (f : X → Y → ℝ) :
    average (fun x => average (fun y => f x y)) = average (fun y => average (fun x => f x y)) := by
  simp only [average, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem average_resample {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [Nonempty X] (i : I) (f : (I → X) → ℝ) :
    average (fun a => average (fun x => f (Function.update a i x))) = average f := by
  rw [← average_prod (fun p : (I → X) × X => f (Function.update p.1 i p.2))]
  have he := average_equiv (resampleSwap (T := X) i) (fun p : (I → X) × X => f p.1)
  change average (fun p : (I → X) × X => f (Function.update p.1 i p.2)) = _ at he
  rw [he, average_prod]
  simp_rw [average_const]

end QueryComplexity.FiniteProbability
