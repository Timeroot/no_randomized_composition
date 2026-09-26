import QueryComplexity.BernoulliSmoothing
import Mathlib.Data.Nat.Choose.Central

namespace QueryComplexity.BernoulliSmoothing

noncomputable def centralMass (m : ℕ) : ℝ := (m.centralBinom : ℝ) / (4 : ℝ) ^ m

theorem centralMass_nonneg (m : ℕ) : 0 ≤ centralMass m := by unfold centralMass; positivity

theorem centralMass_recurrence (m : ℕ) :
    2 * ((m : ℝ) + 1) * centralMass (m + 1) = (2 * (m : ℝ) + 1) * centralMass m := by
  have h : ((m : ℝ) + 1) * ((m + 1).centralBinom : ℝ) =
      2 * (2 * (m : ℝ) + 1) * (m.centralBinom : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ m
  unfold centralMass
  rw [pow_succ]
  field_simp
  linear_combination 2 * h

theorem centralMass_square_lower (m : ℕ) (hm : 1 ≤ m) :
    1 ≤ 4 * (m : ℝ) * centralMass m ^ 2 := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [centralMass, Nat.centralBinom, Nat.choose]
  | succ m hm ih =>
    have hrec := congrArg (fun z : ℝ => z ^ 2) (centralMass_recurrence m)
    have hnon : 0 ≤ (4 * (m : ℝ) * centralMass m ^ 2 - 1) * ((m : ℝ) + 1) :=
      mul_nonneg (by linarith) (by positivity)
    have he : (4 * ((m : ℝ) + 1) * centralMass (m + 1) ^ 2 - 1) * ((m : ℝ) + 1) =
        (4 * (m : ℝ) * centralMass m ^ 2 - 1) * ((m : ℝ) + 1) + centralMass m ^ 2 := by
      nlinarith only [hrec]
    have hprod : 0 ≤ (4 * ((m : ℝ) + 1) * centralMass (m + 1) ^ 2 - 1) * ((m : ℝ) + 1) := by
      rw [he]
      exact add_nonneg hnon (sq_nonneg _)
    have hfactor : 0 ≤ 4 * ((m : ℝ) + 1) * centralMass (m + 1) ^ 2 - 1 :=
      (mul_nonneg_iff_of_pos_right (by positivity : (0 : ℝ) < (m : ℝ) + 1)).mp hprod
    push_cast
    linarith

theorem odd_centralMass_lower (m : ℕ) :
    centralMass m / 2 ≤ fairBinomialMass (2 * m + 1) m := by
  have hc : m.centralBinom ≤ (2 * m + 1).choose m :=
    Nat.choose_le_choose m (by omega : 2 * m ≤ 2 * m + 1)
  have hp : (2 : ℝ) ^ (2 * m + 1) = (4 : ℝ) ^ m * 2 := by
    rw [pow_add, pow_mul]
    norm_num
  unfold centralMass fairBinomialMass
  rw [hp, div_div]
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hc) (by positivity)

theorem fairBinomialMass_odd_square_lower (m : ℕ) (hm : 1 ≤ m) :
    1 / (16 * (m : ℝ)) ≤ fairBinomialMass (2 * m + 1) m ^ 2 := by
  have h := centralMass_square_lower m hm
  have ho := odd_centralMass_lower m
  have ha := centralMass_nonneg m
  have hp : 0 ≤ fairBinomialMass (2 * m + 1) m := by unfold fairBinomialMass; positivity
  have hs : centralMass m ^ 2 ≤ 4 * fairBinomialMass (2 * m + 1) m ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4 * (m : ℝ) by positivity)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * (m : ℝ))).mpr
  nlinarith

end QueryComplexity.BernoulliSmoothing
