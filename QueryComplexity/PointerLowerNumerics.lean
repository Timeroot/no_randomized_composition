import QueryComplexity.CentralBinomialLower

namespace QueryComplexity.PointerLowerNumerics

def arity (s : ℕ) : ℕ := 2 ^ s - 1
def cutoff (s : ℕ) : ℕ := s / 100
def cellBudget (s : ℕ) : ℕ := arity s * arity s * s / 1000000
noncomputable def varianceBound (s : ℕ) : ℝ := (arity s : ℝ) / (16 * (5 : ℝ) ^ cutoff s)

theorem cutoff_pos (s : ℕ) (hs : 1000 ≤ s) : 0 < cutoff s := by unfold cutoff; omega

theorem scale_le_cutoff (s : ℕ) (hs : 1000 ≤ s) : s ≤ 200 * cutoff s := by unfold cutoff; omega

theorem arity_pos (s : ℕ) (hs : 1000 ≤ s) : 0 < arity s := by
  have h := Nat.lt_two_pow_self (n := s)
  unfold arity
  omega

theorem cutoff_le_arity (s : ℕ) (hs : 1000 ≤ s) : 4 * cutoff s ≤ arity s := by
  have h := Nat.lt_two_pow_self (n := s)
  unfold cutoff arity
  omega

theorem exponential_margin (s : ℕ) (hs : 1000 ≤ s) :
    16 * 192 ^ 2 * 25 ^ cutoff s ≤ arity s := by
  have he : 20 + 5 * cutoff s + 1 ≤ s := by unfold cutoff; omega
  have hpower : 25 ^ cutoff s ≤ 2 ^ (5 * cutoff s) := by
    calc
      _ ≤ 32 ^ cutoff s := Nat.pow_le_pow_left (by norm_num : 25 ≤ 32) (cutoff s)
      _ = 2 ^ (5 * cutoff s) := by rw [pow_mul]; norm_num
  have hsmall : 16 * 192 ^ 2 * 25 ^ cutoff s ≤ 2 ^ (20 + 5 * cutoff s) := by
    rw [pow_add]
    exact Nat.mul_le_mul (by norm_num) hpower
  have hlarge : 2 * 2 ^ (20 + 5 * cutoff s) ≤ 2 ^ s := by
    have h := Nat.pow_le_pow_right (by omega : 0 < 2) he
    simpa [pow_succ, Nat.mul_comm] using h
  have hpos : 0 < 2 ^ (20 + 5 * cutoff s) := by positivity
  unfold arity
  omega

theorem varianceBound_pos (s : ℕ) (hs : 1000 ≤ s) : 0 < varianceBound s := by
  unfold varianceBound
  exact div_pos (Nat.cast_pos.mpr (arity_pos s hs)) (by positivity)

theorem inverse_variance_prior_le (s m : ℕ) (hs : 1000 ≤ s)
    (hq : arity s = 2 * m + 1) (π : ℝ) (hπ : 0 ≤ π)
    (hsquare : 1 / (16 * (m : ℝ)) ≤ π ^ 2) :
    1 / (varianceBound s * π) ≤ (1 : ℝ) / 12 := by
  have hm : 0 < m := by
    have h := exponential_margin s hs
    have hp : 0 < 25 ^ cutoff s := by positivity
    omega
  have hmreal : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hqreal : (0 : ℝ) < (arity s : ℝ) := Nat.cast_pos.mpr (arity_pos s hs)
  have hmle : (m : ℝ) ≤ (arity s : ℝ) := by exact_mod_cast (show m ≤ arity s by omega)
  have hp1 : 1 ≤ 16 * (m : ℝ) * π ^ 2 := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * (m : ℝ))).mp hsquare
    nlinarith only [h]
  have hp2 : 1 ≤ 16 * (arity s : ℝ) * π ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmle) (sq_nonneg π)]
  have hp3 := mul_le_mul_of_nonneg_left hp2 hqreal.le
  have hn : 16 * 192 ^ 2 * (5 : ℝ) ^ (2 * cutoff s) ≤ (arity s : ℝ) := by
    have h : (16 : ℝ) * 192 ^ 2 * (25 : ℝ) ^ cutoff s ≤ (arity s : ℝ) := by
      exact_mod_cast exponential_margin s hs
    simpa only [pow_mul, show (5 : ℝ) ^ 2 = 25 by norm_num] using h
  have hsquares : (192 * (5 : ℝ) ^ cutoff s) ^ 2 ≤ ((arity s : ℝ) * π) ^ 2 := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm (cutoff s) 2]
    nlinarith only [hp3, hn]
  have hpositive : 0 < 192 * (5 : ℝ) ^ cutoff s := by positivity
  have hprod : 192 * (5 : ℝ) ^ cutoff s ≤ (arity s : ℝ) * π := by
    have hnon : 0 ≤ (arity s : ℝ) * π := mul_nonneg hqreal.le hπ
    nlinarith
  have hvarprod : (12 : ℝ) ≤ varianceBound s * π := by
    unfold varianceBound
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (5 : ℝ) ^ cutoff s)).mpr
    nlinarith only [hprod]
  exact one_div_le_one_div_of_le (by norm_num) hvarprod

theorem cellBudget_margin (s : ℕ) (hs : 1000 ≤ s) :
    800 * cellBudget s ≤ arity s * arity s * cutoff s := by
  have hdiv : 1000000 * cellBudget s ≤ arity s * arity s * s := by
    unfold cellBudget
    exact Nat.mul_div_le _ _
  have hs' := Nat.mul_le_mul_left (arity s * arity s) (scale_le_cutoff s hs)
  nlinarith only [hdiv, hs']

theorem discovery_markov_le (s : ℕ) (hs : 1000 ≤ s) :
    (2 * (cellBudget s : ℝ) / (arity s : ℝ)) /
      ((arity s : ℝ) * (cutoff s : ℝ) / 8) ≤ (1 : ℝ) / 50 := by
  have hq : (0 : ℝ) < (arity s : ℝ) := Nat.cast_pos.mpr (arity_pos s hs)
  have hr : (0 : ℝ) < (cutoff s : ℝ) := Nat.cast_pos.mpr (cutoff_pos s hs)
  have hm : 800 * (cellBudget s : ℝ) ≤ (arity s : ℝ) * (arity s : ℝ) * (cutoff s : ℝ) := by
    exact_mod_cast cellBudget_margin s hs
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (arity s : ℝ) * (cutoff s : ℝ) / 8)).mpr
  apply (div_le_iff₀ hq).mpr
  nlinarith only [hm]

theorem encoding_budget_lower (s a : ℕ) :
    (a : ℝ) * (arity s : ℝ) ^ 2 * (s : ℝ) / 1000000 ≤
      (((cellBudget s + 1) * (12 * a + 1) : ℕ) : ℝ) := by
  have hfloor : arity s * arity s * s ≤ 1000000 * (cellBudget s + 1) := by
    unfold cellBudget
    omega
  have hr : (arity s : ℝ) ^ 2 * (s : ℝ) ≤ 1000000 * ((cellBudget s : ℝ) + 1) := by
    exact_mod_cast (by simpa only [pow_two] using hfloor :
      arity s ^ 2 * s ≤ 1000000 * (cellBudget s + 1))
  have hm := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg a : (0 : ℝ) ≤ (a : ℝ))
  have hcoef : (a : ℝ) ≤ 12 * (a : ℝ) + 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) a]
  have hmul := mul_le_mul_of_nonneg_left hcoef
    (show (0 : ℝ) ≤ 1000000 * ((cellBudget s : ℝ) + 1) by positivity)
  push_cast
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000)).mpr
  nlinarith only [hm, hmul]

end QueryComplexity.PointerLowerNumerics
