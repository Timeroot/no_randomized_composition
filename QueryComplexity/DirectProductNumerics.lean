import QueryComplexity.DirectProduct

/-! Integer-power estimates for the final coded-cell lower bound. -/

namespace QueryComplexity.DirectProduct

theorem four_copy_decay (h : ℕ) :
    (2 : ℝ) ^ h * ((2 : ℝ) / 3) ^ (4 * h) ≤ ((1 : ℝ) / 2) ^ h := by
  rw [pow_mul, ← mul_pow]
  apply pow_le_pow_left₀ (by norm_num)
  norm_num

theorem quotient_budget_le (ell A Q : ℕ) (hQ : Q ≤ 25 * ell * A) :
    Q / (A + 1) ≤ 25 * ell := by
  apply (Nat.div_le_iff_le_mul_add_pred (Nat.succ_pos A)).2
  nlinarith

/-- The chosen number of copies makes the direct-product list bound smaller
than the `1/6` inclusion probability supplied by the coded-cell hybrid. -/
theorem list_bound_small (ell q A Q L : ℕ) (hell : 1 ≤ ell)
    (hq : q ≤ 2 ^ ell) (hQ : Q ≤ 25 * ell * A) (hL : L ≤ q ^ 3) :
    (L : ℝ) * ((2 : ℝ) ^ (Q / (A + 1)) * ((2 : ℝ) / 3) ^ (100 * ell)) ≤ 1 / 16 := by
  have hquot := quotient_budget_le ell A Q hQ
  have hqR : (q : ℝ) ≤ (2 : ℝ) ^ ell := by exact_mod_cast hq
  have hL' : (L : ℝ) ≤ (2 : ℝ) ^ (3 * ell) := by
    calc
      _ ≤ (q : ℝ) ^ 3 := by exact_mod_cast hL
      _ ≤ ((2 : ℝ) ^ ell) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hqR 3
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hdecay : (2 : ℝ) ^ (25 * ell) * ((2 : ℝ) / 3) ^ (100 * ell) ≤
      ((1 : ℝ) / 2) ^ (25 * ell) := by
    simpa only [show 4 * (25 * ell) = 100 * ell by omega] using four_copy_decay (25 * ell)
  have hpow : (2 : ℝ) ^ (Q / (A + 1)) ≤ (2 : ℝ) ^ (25 * ell) :=
    pow_le_pow_right₀ (by norm_num) hquot
  calc
    _ ≤ (L : ℝ) * ((2 : ℝ) ^ (25 * ell) * ((2 : ℝ) / 3) ^ (100 * ell)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpow (by positivity)) (Nat.cast_nonneg _)
    _ ≤ (L : ℝ) * ((1 : ℝ) / 2) ^ (25 * ell) :=
      mul_le_mul_of_nonneg_left hdecay (Nat.cast_nonneg _)
    _ ≤ (2 : ℝ) ^ (3 * ell) * ((1 : ℝ) / 2) ^ (25 * ell) :=
      mul_le_mul_of_nonneg_right hL' (by positivity)
    _ = ((1 : ℝ) / 2) ^ (22 * ell) := by
      rw [show 25 * ell = 3 * ell + 22 * ell by omega, pow_add]
      rw [← mul_assoc, ← mul_pow]
      norm_num
    _ ≤ ((1 : ℝ) / 2) ^ 4 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ = _ := by norm_num

theorem list_bound_twelfth (ell q A Q L : ℕ) (hell : 1 ≤ ell)
    (hq : q ≤ 2 ^ ell) (hQ : Q ≤ 25 * ell * A) (hL : L ≤ q ^ 3) :
    (L : ℝ) * ((2 : ℝ) ^ (Q / (A + 1)) * ((2 : ℝ) / 3) ^ (100 * ell)) ≤ 1 / 12 :=
  (list_bound_small ell q A Q L hell hq hQ hL).trans (by norm_num)

end QueryComplexity.DirectProduct
