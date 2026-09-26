import ForMathlib.Probability.BernoulliProduct

/-! Exact finite Bernoulli mean and variance, and a one-sided Chebyshev bound. -/

open scoped BigOperators

namespace BernoulliProduct

variable {I : Type*} [Fintype I] [DecidableEq I]

def centered (p : I → ℝ) (x : I → Bool) (i : I) : ℝ :=
  (if x i then 1 else 0) - p i

omit [DecidableEq I] in
theorem centered_sum (p : I → ℝ) (x : I → Bool) :
    (∑ i, centered p x i) = count x - ∑ i, p i := by
  simp only [centered, count, Finset.sum_sub_distrib]

omit [Fintype I] in
theorem split_coordinate_self (i : I) (b : Bool) (rest : {j // j ≠ i} → Bool) :
    ((Equiv.funSplitAt i Bool).symm (b, rest)) i = b := by
  simp [Equiv.funSplitAt, Equiv.piSplitAt]

omit [Fintype I] in
theorem split_coordinate_other (i j : I) (hji : j ≠ i) (b : Bool)
    (rest : {j // j ≠ i} → Bool) :
    ((Equiv.funSplitAt i Bool).symm (b, rest)) j = rest ⟨j, hji⟩ := by
  simp [Equiv.funSplitAt, Equiv.piSplitAt, hji]

theorem coordinate_mean (p : I → ℝ) (i : I) :
    (∑ x, weight p x * (if x i then (1 : ℝ) else 0)) = p i := by
  rw [expectation_split p i]
  simp only [split_coordinate_self, Bool.false_eq_true, if_false, if_true, mul_zero, mul_one, zero_add]
  rw [← Finset.sum_mul, weight_mass, one_mul]

theorem mean_count (p : I → ℝ) : (∑ x, weight p x * count x) = ∑ i, p i := by
  simp only [count, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [coordinate_mean]

theorem centered_coordinate_second (p : I → ℝ) (i : I) :
    (∑ x, weight p x * centered p x i ^ 2) = p i * (1 - p i) := by
  rw [expectation_split p i]
  simp only [centered, split_coordinate_self, Bool.false_eq_true, if_false, if_true]
  have he : (1 - p i) * (0 - p i) ^ 2 + p i * (1 - p i) ^ 2 = p i * (1 - p i) := by ring
  rw [he, ← Finset.sum_mul, weight_mass, one_mul]

theorem centered_covariance_zero (p : I → ℝ) (i j : I) (hij : i ≠ j) :
    (∑ x, weight p x * (centered p x i * centered p x j)) = 0 := by
  rw [expectation_split p i]
  simp only [centered, split_coordinate_self, split_coordinate_other i j (Ne.symm hij),
    Bool.false_eq_true, if_false, if_true]
  apply Finset.sum_eq_zero
  intro rest _
  ring

theorem centered_covariance (p : I → ℝ) (i j : I) :
    (∑ x, weight p x * (centered p x i * centered p x j)) =
      if i = j then p i * (1 - p i) else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [if_true, ← pow_two]
    exact centered_coordinate_second p i
  · simp only [hij, if_false]
    exact centered_covariance_zero p i j hij

/-- The exact variance formula, proved by expanding the square and evaluating
the centered covariances of the finite product distribution. -/
theorem variance_count (p : I → ℝ) :
    (∑ x, weight p x * (count x - ∑ i, p i) ^ 2) = ∑ i, p i * (1 - p i) := by
  calc
    _ = ∑ i, ∑ j, ∑ x, weight p x * (centered p x i * centered p x j) := by
      simp only [← centered_sum, pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    _ = ∑ i, ∑ j, if i = j then p i * (1 - p i) else 0 := by
      simp_rw [centered_covariance]
    _ = _ := by simp

theorem variance_count_le (p : I → ℝ) :
    (∑ x, weight p x * (count x - ∑ i, p i) ^ 2) ≤ (Fintype.card I : ℝ) / 4 := by
  rw [variance_count]
  calc
    _ ≤ ∑ _i : I, (1 : ℝ) / 4 := Finset.sum_le_sum fun i _ => by
      nlinarith [sq_nonneg (p i - 1 / 2)]
    _ = _ := by simp; ring

/-- A finite one-sided Chebyshev bound around the exact sum of Bernoulli
means. The threshold may be real, avoiding floor bookkeeping. -/
theorem upper_tail (p : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (gap : ℝ) (hgap : 0 < gap) :
    (∑ x, if (∑ i, p i) + gap ≤ count x then weight p x else 0) ≤
      (Fintype.card I : ℝ) / (4 * gap ^ 2) := by
  have hmarkov : gap ^ 2 * (∑ x, if (∑ i, p i) + gap ≤ count x then weight p x else 0) ≤
      ∑ x, weight p x * (count x - ∑ i, p i) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    by_cases hx : (∑ i, p i) + gap ≤ count x
    · simp only [hx, if_true]
      have hdiff : gap ≤ count x - ∑ i, p i := by linarith
      have hs := pow_le_pow_left₀ (le_of_lt hgap) hdiff 2
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hs (weight_nonnegative p hp x)
    · simp only [hx, if_false, mul_zero]
      exact mul_nonneg (weight_nonnegative p hp x) (sq_nonneg _)
  have h := hmarkov.trans (variance_count_le p)
  have hg2 : 0 < gap ^ 2 := pow_pos hgap _
  calc
    _ ≤ ((Fintype.card I : ℝ) / 4) / gap ^ 2 :=
      (le_div_iff₀ hg2).2 (by simpa only [mul_comm] using h)
    _ = _ := by ring

theorem upper_tail_of_mean_le (p : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (threshold gap : ℝ) (hgap : 0 < gap) (hmean : (∑ i, p i) + gap ≤ threshold) :
    (∑ x, if threshold < count x then weight p x else 0) ≤
      (Fintype.card I : ℝ) / (4 * gap ^ 2) := by
  refine (Finset.sum_le_sum (fun x _ => ?_)).trans (upper_tail p hp gap hgap)
  by_cases hx : threshold < count x
  · have hm : (∑ i, p i) + gap ≤ count x := hmean.trans (le_of_lt hx)
    simp [hx, hm]
  · simp only [hx, if_false]
    split_ifs
    · exact weight_nonnegative p hp x
    · exact le_refl 0

end BernoulliProduct
