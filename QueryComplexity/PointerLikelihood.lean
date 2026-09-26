import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-! Finite combinatorial and algebraic estimates for the pointer likelihood
ratio. Connecting these counts to a query transcript remains separate. -/

namespace QueryComplexity.PointerLikelihood

theorem choose_drop_one_five (n k : ℕ) (hn : 0 < n)
    (hr : n ≤ 5 * (n - k)) : n.choose k ≤ 5 * (n - 1).choose k := by
  have hrec := Nat.choose_mul_succ_eq (n - 1) k
  have hn' : n - 1 + 1 = n := by omega
  rw [hn'] at hrec
  apply Nat.le_of_mul_le_mul_right ?_ hn
  calc
    n.choose k * n ≤ n.choose k * (5 * (n - k)) := Nat.mul_le_mul_left _ hr
    _ = (5 * (n - 1).choose k) * n := by nlinarith

/-- Avoiding `h` specified columns costs at most a factor `5^h` when the
remaining red proportion stays at least one fifth. -/
theorem choose_avoid_lower (q k h : ℕ) (hh : h ≤ q)
    (hr : 5 * k + 4 * h ≤ 4 * q) :
    q.choose k ≤ 5 ^ h * (q - h).choose k := by
  induction h with
  | zero => simp
  | succ h ih =>
    have hh' : h ≤ q := by omega
    have hr' : 5 * k + 4 * h ≤ 4 * q := by omega
    have hn : 0 < q - h := by omega
    have hstep : q - h ≤ 5 * ((q - h) - k) := by omega
    calc
      q.choose k ≤ 5 ^ h * (q - h).choose k := ih hh' hr'
      _ ≤ 5 ^ h * (5 * (q - h - 1).choose k) :=
        Nat.mul_le_mul_left _ (choose_drop_one_five (q - h) k hn hstep)
      _ = 5 ^ (h + 1) * (q - (h + 1)).choose k := by
        have heq : q - h - 1 = q - (h + 1) := by omega
        rw [heq, pow_succ]
        ring

theorem choose_avoid_probability_lower (q k h : ℕ) (hk : k ≤ q) (hh : h ≤ q)
    (hr : 5 * k + 4 * h ≤ 4 * q) :
    (1 : ℝ) / 5 ^ h ≤ ((q - h).choose k : ℝ) / (q.choose k : ℝ) := by
  have hden : (0 : ℝ) < (q.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  apply (div_le_div_iff₀ (by positivity) hden).2
  have hbound := choose_avoid_lower q k h hh hr
  have h' : (q.choose k : ℝ) ≤ (5 : ℝ) ^ h * ((q - h).choose k : ℝ) := by exact_mod_cast hbound
  simpa [mul_comm] using h'

/-- The actual blue-set size used by the pointer construction satisfies the
previous estimate for all `q ≥ 5` and `h ≤ q/4`. -/
theorem pointer_choose_avoid_probability_lower (q h : ℕ) (hq : 5 ≤ q)
    (hh : 4 * h ≤ q) :
    (1 : ℝ) / 5 ^ h ≤
      ((q - h).choose ((q - 1) / 2 + 1) : ℝ) / (q.choose ((q - 1) / 2 + 1) : ℝ) := by
  apply choose_avoid_probability_lower <;> omega

/-- An equal-prior likelihood ratio `a` gives posterior variance `a/(1+a)^2`. -/
theorem posterior_variance_identity (a : ℝ) (ha : 0 ≤ a) :
    (a / (1 + a)) * (1 - a / (1 + a)) = a / (1 + a) ^ 2 := by
  have hden : 1 + a ≠ 0 := by linarith
  field_simp
  ring

theorem posterior_variance_lower (a r : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hr : r ≤ a) :
    r / 4 ≤ (a / (1 + a)) * (1 - a / (1 + a)) := by
  rw [posterior_variance_identity a ha]
  have hden : 0 < (1 + a) ^ 2 := by positivity
  have hsq : (1 + a) ^ 2 ≤ 4 := by nlinarith
  calc
    r / 4 ≤ a / 4 := div_le_div_of_nonneg_right hr (by norm_num)
    _ ≤ a / (1 + a) ^ 2 := div_le_div_of_nonneg_left ha hden hsq

end QueryComplexity.PointerLikelihood
