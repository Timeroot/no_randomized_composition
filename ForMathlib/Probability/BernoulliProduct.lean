import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic

namespace BernoulliProduct

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def weight (p : I → ℝ) (x : I → Bool) : ℝ :=
  ∏ i, if x i then p i else 1 - p i

def count (x : I → Bool) : ℝ := ∑ i, if x i then (1 : ℝ) else 0

omit [DecidableEq I] in
theorem weight_nonnegative (p : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (x : I → Bool) : 0 ≤ weight p x := by
  refine Finset.prod_nonneg fun i _ => ?_
  cases x i <;> grind [hp i]

omit [DecidableEq I] in
theorem count_nonnegative (x : I → Bool) : 0 ≤ count x := by
  refine Finset.sum_nonneg fun i _ => ?_
  positivity

theorem weight_mass (p : I → ℝ) : ∑ x, weight p x = 1 := by
  have h := Fintype.prod_sum (fun (i : I) (b : Bool) => if b then p i else 1 - p i)
  simpa [weight, Fintype.sum_bool] using h.symm

theorem weight_factor (p : I → ℝ) (x : I → Bool) (i : I) :
    weight p x = (if x i then p i else 1 - p i) *
      weight (fun j : {j // j ≠ i} => p j) (fun j => x j) := by
  rw [weight, Fintype.prod_eq_mul_prod_compl i]
  congr 1
  exact Finset.prod_subtype _ (by simp) _

theorem count_factor (x : I → Bool) (i : I) :
    count x = (if x i then (1 : ℝ) else 0) +
      count (fun j : {j // j ≠ i} => x j) := by
  rw [count, Fintype.sum_eq_add_sum_compl i]
  congr 1
  exact Finset.sum_subtype _ (by simp) _

theorem weight_split (p : I → ℝ) (i : I) (b : Bool)
    (rest : {j // j ≠ i} → Bool) :
    weight p ((Equiv.funSplitAt i Bool).symm (b, rest)) =
      (if b then p i else 1 - p i) * weight (fun j : {j // j ≠ i} => p j) rest := by
  rw [weight_factor p _ i]
  have hrest : (fun j : {j // j ≠ i} => ((Equiv.funSplitAt i Bool).symm (b, rest)) j) =
      rest := by
    funext j
    simp [Equiv.funSplitAt, Equiv.piSplitAt, j.2]
  rw [hrest]
  simp [Equiv.funSplitAt, Equiv.piSplitAt]

theorem count_split (i : I) (b : Bool) (rest : {j // j ≠ i} → Bool) :
    count ((Equiv.funSplitAt i Bool).symm (b, rest)) =
      (if b then (1 : ℝ) else 0) + count rest := by
  rw [count_factor _ i]
  have hrest : (fun j : {j // j ≠ i} => ((Equiv.funSplitAt i Bool).symm (b, rest)) j) =
      rest := by
    funext j
    simp [Equiv.funSplitAt, Equiv.piSplitAt, j.2]
  rw [hrest]
  simp [Equiv.funSplitAt, Equiv.piSplitAt]

theorem sum_split (i : I) (f : (I → Bool) → ℝ) :
    ∑ x, f x = ∑ b : Bool, ∑ rest : {j // j ≠ i} → Bool,
      f ((Equiv.funSplitAt i Bool).symm (b, rest)) := by
  simpa only [Fintype.sum_prod_type] using
    (Equiv.sum_comp (Equiv.funSplitAt i Bool).symm f).symm

theorem expectation_split (p : I → ℝ) (i : I) (f : (I → Bool) → ℝ) :
    ∑ x, weight p x * f x =
      ∑ rest : {j // j ≠ i} → Bool, weight (fun j : {j // j ≠ i} => p j) rest *
        ((1 - p i) * f ((Equiv.funSplitAt i Bool).symm (false, rest)) +
          p i * f ((Equiv.funSplitAt i Bool).symm (true, rest))) := by
  rw [sum_split i]
  simp only [Fintype.sum_bool, weight_split, Bool.false_eq_true, ↓reduceIte]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun rest _ => ?_
  ring

theorem coordinate_reciprocal_bound (p : I → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (i : I) :
    p i * (∑ x, weight p x * (count x + 1)⁻¹) ≤
      ∑ x, weight p x * (if x i then (count x)⁻¹ else 0) := by
  rw [expectation_split p i, expectation_split p i]
  simp only [count_split, Bool.false_eq_true, ↓reduceIte, zero_add]
  have heval (b : Bool) (rest : {j // j ≠ i} → Bool) :
      ((Equiv.funSplitAt i Bool).symm (b, rest)) i = b := by
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  simp only [heval, Bool.false_eq_true, ↓reduceIte, mul_zero, zero_add]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun rest _ => ?_
  have hm := count_nonnegative rest
  have hinv : (1 + count rest + 1)⁻¹ ≤ (count rest + 1)⁻¹ := by
    exact inv_anti₀ (by positivity) (by grind)
  have hmix : (1 - p i) * (count rest + 1)⁻¹ +
      p i * (1 + count rest + 1)⁻¹ ≤ (count rest + 1)⁻¹ := by
    have := mul_le_mul_of_nonneg_left hinv (hp i).1
    nlinarith
  have hw := weight_nonnegative (fun j : {j // j ≠ i} => p j) (fun j => hp j) rest
  calc
    _ = (weight (fun j : {j // j ≠ i} => p j) rest * p i) *
        ((1 - p i) * (count rest + 1)⁻¹ + p i * (1 + count rest + 1)⁻¹) := by ring
    _ ≤ (weight (fun j : {j // j ≠ i} => p j) rest * p i) * (count rest + 1)⁻¹ :=
      mul_le_mul_of_nonneg_left hmix (mul_nonneg hw (hp i).1)
    _ = _ := by ring

omit [DecidableEq I] in
theorem coordinate_fraction_sum_le_one (x : I → Bool) :
    (∑ i, if x i then (count x)⁻¹ else 0) ≤ 1 := by
  have heq : (∑ i, if x i then (count x)⁻¹ else 0) = count x * (count x)⁻¹ := by
    rw [count, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases x i <;> simp
  rw [heq]
  by_cases hzero : count x = 0
  · simp [hzero]
  · rw [mul_inv_cancel₀ hzero]

/-- A sharp reciprocal-moment estimate for a sum of independent Bernoullis.
No tail bound is needed. -/
theorem mean_mul_reciprocal_moment_le_one (p : I → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    (∑ i, p i) * (∑ x, weight p x * (count x + 1)⁻¹) ≤ 1 := by
  calc
    _ = ∑ i, p i * (∑ x, weight p x * (count x + 1)⁻¹) := by rw [Finset.sum_mul]
    _ ≤ ∑ i, ∑ x, weight p x * (if x i then (count x)⁻¹ else 0) :=
      Finset.sum_le_sum (fun i _ => coordinate_reciprocal_bound p hp i)
    _ = ∑ x, weight p x * (∑ i, if x i then (count x)⁻¹ else 0) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ ≤ ∑ x, weight p x := by
      refine Finset.sum_le_sum fun x _ => ?_
      simpa using mul_le_mul_of_nonneg_left (coordinate_fraction_sum_le_one x)
        (weight_nonnegative p hp x)
    _ = 1 := weight_mass p

theorem reciprocal_moment_bound (p : I → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hmean : 0 < ∑ i, p i) :
    (∑ x, weight p x * (count x + 1)⁻¹) ≤ 1 / (∑ i, p i) := by
  exact (le_div_iff₀ hmean).2 (by simpa [mul_comm] using mean_mul_reciprocal_moment_le_one p hp)

end BernoulliProduct
