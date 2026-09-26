import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic
import ForMathlib.Probability.BernoulliProduct
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Basic

/-! Binomial coefficients, Boolean count levels, and smoothing estimates. -/

section

/-!
# Elementary smoothing estimates

Bounds on central binomial coefficients and differences between adjacent
point probabilities of fair binomial distributions and their mixtures.
-/

namespace BernoulliSmoothing

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
      refine Finset.sum_le_sum fun j hj => ?_
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

theorem fairBinomialMass_pos (n k : ℕ) (hk : k ≤ n) :
    0 < fairBinomialMass n k := by
  exact div_pos (by exact_mod_cast Nat.choose_pos hk) (by positivity)

/-- Complementation preserves the fair binomial distribution. -/
theorem fairBinomialMass_symm {n k : ℕ} (hk : k ≤ n) :
    fairBinomialMass n (n - k) = fairBinomialMass n k := by
  simp only [fairBinomialMass, Nat.choose_symm hk]

theorem fairBinomialMass_middle_succ (m : ℕ) :
    fairBinomialMass (2 * m + 1) (m + 1) = fairBinomialMass (2 * m + 1) m := by
  simpa only [show 2 * m + 1 - m = m + 1 by omega] using
    fairBinomialMass_symm (show m ≤ 2 * m + 1 by omega)

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
      refine Finset.sum_le_sum fun a _ => ?_
      rw [← mul_sub, abs_mul, abs_of_nonneg (hw a)]
      apply mul_le_mul_of_nonneg_left _ (hw a)
      have harg : k + 1 - shift a = (k - shift a) + 1 := by omega
      rw [harg]
      exact fairBinomialMassInt_adjacent (size a) (k - shift a)

end BernoulliSmoothing

end

section

namespace BoolCounting

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

def trueSet (x : I → Bool) : Finset I := Finset.univ.filter (fun i => x i = true)

def ofSet (s : Finset I) : I → Bool := fun i => decide (i ∈ s)

@[simp] theorem trueSet_ofSet (s : Finset I) : trueSet (ofSet s) = s := by
  ext i
  simp [trueSet, ofSet]

@[simp] theorem ofSet_trueSet (x : I → Bool) : ofSet (trueSet x) = x := by
  funext i
  simp [ofSet, trueSet]

def levelEquiv (k : ℕ) :
    {x : I → Bool // (trueSet x).card = k} ≃
      {s : Finset I // s ∈ Finset.univ.powersetCard k} where
  toFun x := ⟨trueSet x.1, by simp [x.2]⟩
  invFun s := ⟨ofSet s.1, by
    rw [trueSet_ofSet]
    exact (Finset.mem_powersetCard.mp s.2).2⟩
  left_inv x := by ext; simp
  right_inv s := by ext; simp

theorem level_card (k : ℕ) :
    Fintype.card {x : I → Bool // (trueSet x).card = k} = (Fintype.card I).choose k := by
  have h := Fintype.card_congr (levelEquiv (I := I) k)
  simpa using h

omit [DecidableEq I] in
theorem count_eq_card (x : I → Bool) :
    BernoulliProduct.count x = ((trueSet x).card : ℝ) := by
  simp only [BernoulliProduct.count, trueSet, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  cases x i <;> rfl

theorem fair_count_mass (k : ℕ) :
    (∑ x : I → Bool, if (trueSet x).card = k then
      (1 : ℝ) / 2 ^ Fintype.card I else 0) =
      BernoulliSmoothing.fairBinomialMass (Fintype.card I) k := by
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter (fun x : I → Bool => (trueSet x).card = k)).card =
      (Fintype.card I).choose k := by
    simpa only [Fintype.card_subtype] using level_card (I := I) k
  rw [hcard]
  simp [BernoulliSmoothing.fairBinomialMass, div_eq_mul_inv]

theorem fair_count_mass_int (k : ℤ) :
    (∑ x : I → Bool, if ((trueSet x).card : ℤ) = k then
      (1 : ℝ) / 2 ^ Fintype.card I else 0) =
      BernoulliSmoothing.fairBinomialMassInt (Fintype.card I) k := by
  by_cases hk : 0 ≤ k
  · rw [BernoulliSmoothing.fairBinomialMassInt, if_pos hk]
    have heq : ∀ x : I → Bool, (((trueSet x).card : ℤ) = k) ↔ (trueSet x).card = k.toNat := by
      intro x
      omega
    simp_rw [heq]
    exact fair_count_mass k.toNat
  · rw [BernoulliSmoothing.fairBinomialMassInt, if_neg hk]
    apply Finset.sum_eq_zero
    intro x _
    rw [if_neg (by omega)]

end BoolCounting

namespace BernoulliSmoothing

open scoped BigOperators

variable {I : Type*} [Fintype I]

/-- The uniform Boolean law conditioned on exactly `k` true coordinates. -/
noncomputable def fairLayerWeight (k : ℕ) (x : I → Bool) : ℝ :=
  (if (BoolCounting.trueSet x).card = k then (1 : ℝ) / 2 ^ Fintype.card I else 0) /
    fairBinomialMass (Fintype.card I) k

theorem fairLayerWeight_nonneg (k : ℕ) (x : I → Bool) : 0 ≤ fairLayerWeight k x := by
  unfold fairLayerWeight fairBinomialMass
  split_ifs <;> positivity

theorem sum_fairLayerWeight [DecidableEq I] (k : ℕ) (hk : k ≤ Fintype.card I) :
    ∑ x : I → Bool, fairLayerWeight k x = 1 := by
  classical
  simp only [fairLayerWeight, ← Finset.sum_div, BoolCounting.fair_count_mass]
  exact div_self (fairBinomialMass_pos _ k hk).ne'

end BernoulliSmoothing

end

section

namespace BernoulliSmoothing

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

end BernoulliSmoothing

end

section

/-! Lower bounds for the probability that a uniform fixed-size set avoids specified points. -/

namespace BinomialAvoidance

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

end BinomialAvoidance

end

section

/-! Pointed subsets and their avoidance probabilities. -/

namespace PointedSetCounting

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev PointedChoice (I : Type*) [Fintype I] (k : ℕ) :=
  {choice : Finset I × I // choice.2 ∈ choice.1 ∧ choice.1.card = k}

def choiceEquiv (k : ℕ) :
    PointedChoice I k ≃ Σ s : {s : Finset I // s ∈ Finset.univ.powersetCard k}, s.1 where
  toFun c := ⟨⟨c.1.1, by simp [c.2.2]⟩, ⟨c.1.2, c.2.1⟩⟩
  invFun s := ⟨(s.1.1, s.2.1), s.2.2, (Finset.mem_powersetCard.mp s.1.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem choice_card (k : ℕ) :
    Fintype.card (PointedChoice I k) = (Fintype.card I).choose k * k := by
  classical
  rw [Fintype.card_congr (choiceEquiv (I := I) k), Fintype.card_sigma]
  have heq : ∀ s : {s : Finset I // s ∈ Finset.univ.powersetCard k},
      Fintype.card s.1 = k := by
    intro s
    simpa using (Finset.mem_powersetCard.mp s.2).2
  simp_rw [heq]
  simp

noncomputable def avoidChoiceEquiv (D : Finset I) (k : ℕ) :
    {c : PointedChoice I k // Disjoint c.1.1 D} ≃
      Σ s : {s : Finset I // s ∈ Dᶜ.powersetCard k}, s.1 where
  toFun c := ⟨⟨c.1.1.1, Finset.mem_powersetCard.mpr ⟨by
    intro i hi
    exact Finset.mem_compl.mpr (fun hD => Finset.disjoint_left.mp c.2 hi hD), c.1.2.2⟩⟩,
    ⟨c.1.1.2, c.1.2.1⟩⟩
  invFun s := ⟨⟨(s.1.1, s.2.1), s.2.2, (Finset.mem_powersetCard.mp s.1.2).2⟩, by
    apply Finset.disjoint_left.mpr
    intro i hi hD
    exact Finset.mem_compl.mp ((Finset.mem_powersetCard.mp s.1.2).1 hi) hD⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem avoid_choice_card (D : Finset I) (k : ℕ) :
    Fintype.card {c : PointedChoice I k // Disjoint c.1.1 D} =
      (Fintype.card I - D.card).choose k * k := by
  classical
  rw [Fintype.card_congr (avoidChoiceEquiv D k), Fintype.card_sigma]
  have heq : ∀ s : {s : Finset I // s ∈ Dᶜ.powersetCard k}, Fintype.card s.1 = k := by
    intro s
    simpa using (Finset.mem_powersetCard.mp s.2).2
  simp_rw [heq]
  simp [Finset.card_compl]

theorem avoidance_probability (D : Finset I) (k : ℕ) (hk : 0 < k) :
    (Fintype.card {c : PointedChoice I k // Disjoint c.1.1 D} : ℝ) /
        (Fintype.card (PointedChoice I k) : ℝ) =
      ((Fintype.card I - D.card).choose k : ℝ) / ((Fintype.card I).choose k : ℝ) := by
  rw [avoid_choice_card, choice_card]
  push_cast
  exact mul_div_mul_right _ _ (by exact_mod_cast hk.ne' : (k : ℝ) ≠ 0)

end PointedSetCounting

end
