import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-!
# Elementary smoothing estimates

This file develops the finite counting estimates needed for the posterior
majority argument.  It does not assert a majority query lower bound.
-/

namespace QueryComplexity.BernoulliSmoothing

open scoped BigOperators

theorem choose_mono_below_half {n a b : ℕ} (hab : a ≤ b) (hb : b ≤ n / 2) :
    n.choose a ≤ n.choose b := by
  induction hab using Nat.decreasingInduction with
  | self => rfl
  | of_succ k hk ih =>
    exact (Nat.choose_le_succ_of_lt_half_left (hk.trans_le hb)).trans ih

theorem choose_ge_on_central_interval {n k j : ℕ}
    (hk : 2 * k ≤ n) (hjk : k ≤ j) (hjn : j ≤ n - k) :
    n.choose k ≤ n.choose j := by
  by_cases hjhalf : j ≤ n / 2
  · exact choose_mono_below_half hjk hjhalf
  · rw [← Nat.choose_symm (show j ≤ n by omega)]
    apply choose_mono_below_half <;> omega

theorem choose_central_interval_bound {n k : ℕ} (hk : 2 * k ≤ n) :
    (n - 2 * k + 1) * n.choose k ≤ 2 ^ n := by
  classical
  calc
    (n - 2 * k + 1) * n.choose k =
        ∑ _j ∈ Finset.Icc k (n - k), n.choose k := by
      have hcard : (Finset.Icc k (n - k)).card = n - 2 * k + 1 := by
        rw [Nat.card_Icc]
        omega
      simp [hcard]
    _ ≤ ∑ j ∈ Finset.Icc k (n - k), n.choose j := by
      apply Finset.sum_le_sum
      intro j hj
      exact choose_ge_on_central_interval hk
        (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
    _ ≤ ∑ j ∈ Finset.range (n + 1), n.choose j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        have := (Finset.mem_Icc.mp hj).2
        exact Finset.mem_range.mpr (by omega)
      · intros
        exact Nat.zero_le _
    _ = 2 ^ n := Nat.sum_range_choose n

theorem choose_weighted_distance_bound (n k : ℕ) :
    |(n : ℝ) - 2 * k| * (n.choose k : ℝ) ≤ (2 : ℝ) ^ n := by
  by_cases hkn : k ≤ n
  · by_cases hhalf : 2 * k ≤ n
    · have hbound := choose_central_interval_bound hhalf
      have hbound' : ((n - 2 * k : ℕ) : ℝ) * (n.choose k : ℝ) ≤ (2 : ℝ) ^ n := by
        exact_mod_cast (Nat.le_trans
          (Nat.mul_le_mul_right (n.choose k) (Nat.le_succ (n - 2 * k))) hbound)
      rw [Nat.cast_sub hhalf] at hbound'
      have hhalfR : 2 * (k : ℝ) ≤ n := by exact_mod_cast hhalf
      rw [abs_of_nonneg (by linarith)]
      simpa using hbound'
    · have hhalf' : 2 * (n - k) ≤ n := by omega
      have hbound := choose_central_interval_bound hhalf'
      have hbound' : ((n - 2 * (n - k) : ℕ) : ℝ) *
          (n.choose (n - k) : ℝ) ≤ (2 : ℝ) ^ n := by
        exact_mod_cast (Nat.le_trans
          (Nat.mul_le_mul_right (n.choose (n - k))
            (Nat.le_succ (n - 2 * (n - k)))) hbound)
      rw [Nat.choose_symm hkn, Nat.cast_sub hhalf', Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_sub hkn] at hbound'
      have hhalfR : (n : ℝ) < 2 * k := by exact_mod_cast (by omega : n < 2 * k)
      rw [abs_of_nonpos (by linarith)]
      nlinarith
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

noncomputable def fairBinomialMass (m k : ℕ) : ℝ := (m.choose k : ℝ) / (2 : ℝ) ^ m

/-- Adjacent masses of a fair binomial differ by at most `2/(m+1)`.
The proof uses only Pascal's identity and central-interval counting. -/
theorem fairBinomialMass_adjacent (m k : ℕ) :
    |fairBinomialMass m (k + 1) - fairBinomialMass m k| ≤ 2 / ((m : ℝ) + 1) := by
  by_cases hk : k ≤ m
  · have hrec : ((m + 1).choose (k + 1) : ℝ) =
        (m.choose k : ℝ) + (m.choose (k + 1) : ℝ) := by
      exact_mod_cast Nat.choose_succ_succ m k
    have hprod : (m.choose (k + 1) : ℝ) * ((m : ℝ) + 1) =
        ((m + 1).choose (k + 1) : ℝ) * (((m + 1) - (k + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_mul_succ_eq m (k + 1)
    rw [Nat.cast_sub (show k + 1 ≤ m + 1 by omega)] at hprod
    push_cast at hprod
    have hid : ((m.choose (k + 1) : ℝ) - (m.choose k : ℝ)) * ((m : ℝ) + 1) =
        ((m : ℝ) + 1 - 2 * ((k : ℝ) + 1)) * ((m + 1).choose (k + 1) : ℝ) := by
      nlinarith
    have habs : |(m.choose (k + 1) : ℝ) - (m.choose k : ℝ)| * ((m : ℝ) + 1) ≤
        (2 : ℝ) ^ (m + 1) := by
      calc
        _ = |((m.choose (k + 1) : ℝ) - (m.choose k : ℝ)) * ((m : ℝ) + 1)| := by
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (m : ℝ) + 1)]
        _ = |(m : ℝ) + 1 - 2 * ((k : ℝ) + 1)| * ((m + 1).choose (k + 1) : ℝ) := by
          rw [hid, abs_mul, abs_of_nonneg
            (show 0 ≤ ((m + 1).choose (k + 1) : ℝ) by positivity)]
        _ ≤ (2 : ℝ) ^ (m + 1) := by
          simpa only [Nat.cast_add, Nat.cast_one] using choose_weighted_distance_bound (m + 1) (k + 1)
    simp only [fairBinomialMass, ← sub_div, abs_div,
      abs_of_pos (by positivity : 0 < (2 : ℝ) ^ m)]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    simpa [pow_succ, mul_comm] using habs
  · have hzero0 : m.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hzero1 : m.choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp only [fairBinomialMass, hzero0, hzero1, Nat.cast_zero, zero_div, sub_self, abs_zero]
    positivity

theorem fairBinomialMass_zero (m : ℕ) :
    fairBinomialMass m 0 ≤ 2 / ((m : ℝ) + 1) := by
  have hnat : m + 1 ≤ 2 ^ (m + 1) := by
    simpa using Nat.choose_le_two_pow (m + 1) 1
  have hreal : (m : ℝ) + 1 ≤ (2 : ℝ) ^ (m + 1) := by exact_mod_cast hnat
  simp only [fairBinomialMass, Nat.choose_zero_right, Nat.cast_one]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  simpa [pow_succ, mul_comm] using hreal

/-- Extension by zero lets shifts and boundary values be treated uniformly. -/
noncomputable def fairBinomialMassInt (m : ℕ) (k : ℤ) : ℝ :=
  if 0 ≤ k then fairBinomialMass m k.toNat else 0

theorem fairBinomialMassInt_adjacent (m : ℕ) (k : ℤ) :
    |fairBinomialMassInt m (k + 1) - fairBinomialMassInt m k| ≤
      2 / ((m : ℝ) + 1) := by
  by_cases hk : 0 ≤ k
  · have hk1 : 0 ≤ k + 1 := by omega
    simp only [fairBinomialMassInt, if_pos hk, if_pos hk1]
    have hnat : (k + 1).toNat = k.toNat + 1 := by omega
    rw [hnat]
    exact fairBinomialMass_adjacent m k.toNat
  · by_cases hk1 : 0 ≤ k + 1
    · have heq : k + 1 = 0 := by omega
      simp only [fairBinomialMassInt, if_neg hk, sub_zero, heq, Int.toNat_zero]
      rw [abs_of_nonneg (by unfold fairBinomialMass; positivity)]
      exact fairBinomialMass_zero m
    · simp only [fairBinomialMassInt, if_neg hk1, if_neg hk, sub_self, abs_zero]
      positivity

/-- A mixture of shifted fair binomials inherits the averaged adjacent-mass
bound. The subsequent Bernoulli argument supplies this mixture explicitly. -/
theorem shifted_mixture_adjacent {A : Type*} [Fintype A]
    (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (size : A → ℕ) (shift : A → ℤ) (k : ℤ) :
    |(∑ a, w a * fairBinomialMassInt (size a) (k + 1 - shift a)) -
      (∑ a, w a * fairBinomialMassInt (size a) (k - shift a))| ≤
      ∑ a, w a * (2 / ((size a : ℝ) + 1)) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a, |w a * fairBinomialMassInt (size a) (k + 1 - shift a) -
        w a * fairBinomialMassInt (size a) (k - shift a)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a _
      rw [← mul_sub, abs_mul, abs_of_nonneg (hw a)]
      apply mul_le_mul_of_nonneg_left _ (hw a)
      have harg : k + 1 - shift a = (k - shift a) + 1 := by omega
      rw [harg]
      exact fairBinomialMassInt_adjacent (size a) (k - shift a)

end QueryComplexity.BernoulliSmoothing
