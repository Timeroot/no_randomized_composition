import QueryComplexity.BernoulliProduct
import QueryComplexity.BernoulliSmoothing
import QueryComplexity.BoolCounting

namespace QueryComplexity.BernoulliMixture

open scoped BigOperators

noncomputable def rate (p : ℝ) : ℝ := if p ≤ 1 / 2 then 2 * p else 2 * (1 - p)

noncomputable def baseline (p : ℝ) : Bool := decide (1 / 2 < p)

theorem rate_bounds {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ rate p ∧ rate p ≤ 1 := by
  unfold rate
  split_ifs with h <;> constructor <;> linarith

theorem rate_ge_variance (p : ℝ) :
    2 * p * (1 - p) ≤ rate p := by
  unfold rate
  split_ifs with h <;> nlinarith [sq_nonneg p, sq_nonneg (1 - p)]

theorem scalar_mixture (p : ℝ) (b : Bool) :
    (if b then p else 1 - p) =
      ∑ selector : Bool, (if selector then rate p else 1 - rate p) *
        (if selector then (1 : ℝ) / 2 else if b = baseline p then 1 else 0) := by
  by_cases h : p ≤ 1 / 2
  · have hbase : baseline p = false := by
      simp only [baseline, decide_eq_false_iff_not]
      exact not_lt.mpr h
    have hrate : rate p = 2 * p := if_pos h
    cases b <;> simp only [Fintype.sum_bool, hrate, hbase,
      Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] <;> ring
  · have hbase : baseline p = true := by
      simp only [baseline, decide_eq_true_eq]
      exact lt_of_not_ge h
    have hrate : rate p = 2 * (1 - p) := if_neg h
    cases b <;> simp only [Fintype.sum_bool, hrate, hbase,
      Bool.false_eq_true, ↓reduceIte] <;> ring

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def componentWeight (p : I → ℝ) (selector x : I → Bool) : ℝ :=
  ∏ i, if selector i then (1 : ℝ) / 2 else if x i = baseline (p i) then 1 else 0

def Compatible (p : I → ℝ) (selector x : I → Bool) : Prop :=
  ∀ i, selector i = false → x i = baseline (p i)

noncomputable instance compatibleDecidable (p : I → ℝ) (selector x : I → Bool) :
    Decidable (Compatible p selector x) := by
  unfold Compatible
  infer_instance

omit [DecidableEq I] in
theorem componentWeight_eq_compatible (p : I → ℝ) (selector x : I → Bool) :
    componentWeight p selector x =
      if Compatible p selector x then
        (1 : ℝ) / 2 ^ (BoolCounting.trueSet selector).card else 0 := by
  classical
  by_cases h : Compatible p selector x
  · rw [if_pos h]
    have hfactor : ∀ i,
        (if selector i then (1 : ℝ) / 2 else if x i = baseline (p i) then 1 else 0) =
          if selector i then (1 : ℝ) / 2 else 1 := by
      intro i
      cases hs : selector i
      · simp [h i hs]
      · simp
    simp only [componentWeight, hfactor]
    rw [Finset.prod_ite]
    simp [BoolCounting.trueSet]
  · rw [if_neg h]
    unfold Compatible at h
    push_neg at h
    obtain ⟨i, hi, hbad⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi, hbad]

noncomputable def activeBitsEquiv (p : I → ℝ) (selector : I → Bool) :
    ({i // selector i = true} → Bool) ≃ {x : I → Bool // Compatible p selector x} where
  toFun bits := ⟨fun i => if h : selector i = true then bits ⟨i, h⟩ else baseline (p i), by
    intro i hi
    simp [hi]⟩
  invFun x i := x.1 i
  left_inv bits := by
    funext i
    simp [i.2]
  right_inv x := by
    ext i
    by_cases hi : selector i = true
    · simp [hi]
    · have hi' : selector i = false := by
        cases hs : selector i
        · rfl
        · exact False.elim (hi hs)
      simp [hi, x.2 i hi']

noncomputable def shift (p : I → ℝ) (selector : I → Bool) : ℕ :=
  (BoolCounting.trueSet (fun i : {i // selector i ≠ true} => baseline (p i))).card

omit [DecidableEq I] in
theorem compatible_count (p : I → ℝ) (selector x : I → Bool)
    (hx : Compatible p selector x) :
    (BoolCounting.trueSet x).card =
      (BoolCounting.trueSet (fun i : {i // selector i = true} => x i)).card + shift p selector := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun i => selector i = true) (fun i => if x i then (1 : ℝ) else 0)
  have hout : (fun i : {i // selector i ≠ true} => x i) =
      (fun i : {i // selector i ≠ true} => baseline (p i)) := by
    funext i
    apply hx i
    cases h : selector i
    · rfl
    · exact False.elim (i.2 h)
  change BernoulliProduct.count (fun i : {i // selector i = true} => x i) +
      BernoulliProduct.count (fun i : {i // selector i ≠ true} => x i) =
        BernoulliProduct.count x at hsplit
  rw [hout] at hsplit
  simp_rw [BoolCounting.count_eq_card] at hsplit
  exact_mod_cast hsplit.symm

theorem activeBits_count (p : I → ℝ) (selector : I → Bool)
    (bits : {i // selector i = true} → Bool) :
    (BoolCounting.trueSet (activeBitsEquiv p selector bits).1).card =
      (BoolCounting.trueSet bits).card + shift p selector := by
  have h := compatible_count p selector (activeBitsEquiv p selector bits).1
    (activeBitsEquiv p selector bits).2
  change (BoolCounting.trueSet (activeBitsEquiv p selector bits).1).card =
    (BoolCounting.trueSet ((activeBitsEquiv p selector).symm (activeBitsEquiv p selector bits))).card +
      shift p selector at h
  simpa only [Equiv.symm_apply_apply] using h

/-- Conditional on the selector, the number of one bits is exactly a shifted
fair binomial, including all boundary values. -/
theorem component_count_mass (p : I → ℝ) (selector : I → Bool) (k : ℤ) :
    (∑ x : I → Bool, if ((BoolCounting.trueSet x).card : ℤ) = k then
      componentWeight p selector x else 0) =
      BernoulliSmoothing.fairBinomialMassInt (BoolCounting.trueSet selector).card
        (k - shift p selector) := by
  classical
  have hsize : Fintype.card {i // selector i = true} = (BoolCounting.trueSet selector).card := by
    simp [Fintype.card_subtype, BoolCounting.trueSet]
  calc
    _ = ∑ x : {x : I → Bool // Compatible p selector x},
        if ((BoolCounting.trueSet x.1).card : ℤ) = k then
          (1 : ℝ) / 2 ^ (BoolCounting.trueSet selector).card else 0 := by
      apply Finset.sum_congr_set {x : I → Bool | Compatible p selector x}
      · intro x hx
        change Compatible p selector x at hx
        rw [componentWeight_eq_compatible, if_pos hx]
      · intro x hx
        change ¬ Compatible p selector x at hx
        rw [componentWeight_eq_compatible, if_neg hx]
        simp
    _ = ∑ bits : {i // selector i = true} → Bool,
        if ((BoolCounting.trueSet (activeBitsEquiv p selector bits).1).card : ℤ) = k then
          (1 : ℝ) / 2 ^ (BoolCounting.trueSet selector).card else 0 :=
      (Equiv.sum_comp (activeBitsEquiv p selector) _).symm
    _ = ∑ bits : {i // selector i = true} → Bool,
        if ((BoolCounting.trueSet bits).card : ℤ) = k - shift p selector then
          (1 : ℝ) / 2 ^ Fintype.card {i // selector i = true} else 0 := by
      apply Finset.sum_congr rfl
      intro bits _
      rw [activeBits_count, hsize]
      have heq : (((BoolCounting.trueSet bits).card + shift p selector : ℕ) : ℤ) = k ↔
          ((BoolCounting.trueSet bits).card : ℤ) = k - shift p selector := by omega
      simp only [heq]
    _ = _ := by
      rw [BoolCounting.fair_count_mass_int, hsize]

/-- Independent Bernoullis are exactly a mixture of deterministic bits and
independent fair bits, with independent selectors. -/
theorem product_mixture (p : I → ℝ) (x : I → Bool) :
    BernoulliProduct.weight p x =
      ∑ selector : I → Bool, BernoulliProduct.weight (fun i => rate (p i)) selector *
        componentWeight p selector x := by
  unfold BernoulliProduct.weight componentWeight
  calc
    _ = ∏ i, ∑ selector : Bool, (if selector then rate (p i) else 1 - rate (p i)) *
        (if selector then (1 : ℝ) / 2 else if x i = baseline (p i) then 1 else 0) := by
      apply Finset.prod_congr rfl
      intro i _
      exact scalar_mixture (p i) (x i)
    _ = ∑ selector : I → Bool, ∏ i,
        (if selector i then rate (p i) else 1 - rate (p i)) *
        (if selector i then (1 : ℝ) / 2 else if x i = baseline (p i) then 1 else 0) :=
      Fintype.prod_sum _
    _ = _ := by simp only [Finset.prod_mul_distrib]

omit [DecidableEq I] in
theorem componentWeight_nonnegative (p : I → ℝ) (selector x : I → Bool) :
    0 ≤ componentWeight p selector x := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> norm_num

theorem componentWeight_mass (p : I → ℝ) (selector : I → Bool) :
    ∑ x, componentWeight p selector x = 1 := by
  have h := Fintype.prod_sum (fun (i : I) (b : Bool) =>
    if selector i then (1 : ℝ) / 2 else if b = baseline (p i) then 1 else 0)
  have hscalar : ∀ i, (∑ b : Bool,
      if selector i then (1 : ℝ) / 2 else if b = baseline (p i) then 1 else 0) = 1 := by
    intro i
    cases selector i <;> cases baseline (p i) <;> norm_num [Fintype.sum_bool]
  simpa only [componentWeight, hscalar, Finset.prod_const_one] using h.symm

noncomputable def countMass (p : I → ℝ) (k : ℤ) : ℝ :=
  ∑ x : I → Bool, if ((BoolCounting.trueSet x).card : ℤ) = k then
    BernoulliProduct.weight p x else 0

theorem countMass_mixture (p : I → ℝ) (k : ℤ) :
    countMass p k = ∑ selector : I → Bool,
      BernoulliProduct.weight (fun i => rate (p i)) selector *
        BernoulliSmoothing.fairBinomialMassInt (BoolCounting.trueSet selector).card
          (k - shift p selector) := by
  unfold countMass
  calc
    _ = ∑ x : I → Bool, ∑ selector : I → Bool,
        BernoulliProduct.weight (fun i => rate (p i)) selector *
          (if ((BoolCounting.trueSet x).card : ℤ) = k then componentWeight p selector x else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [product_mixture]
      split_ifs <;> simp
    _ = ∑ selector : I → Bool, BernoulliProduct.weight (fun i => rate (p i)) selector *
        (∑ x : I → Bool,
          if ((BoolCounting.trueSet x).card : ℤ) = k then componentWeight p selector x else 0) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ = _ := by simp_rw [component_count_mass]

theorem countMass_adjacent_rate (p : I → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hmean : 0 < ∑ i, rate (p i)) (k : ℤ) :
    |countMass p (k + 1) - countMass p k| ≤ 2 / (∑ i, rate (p i)) := by
  have hr : ∀ i, 0 ≤ rate (p i) ∧ rate (p i) ≤ 1 :=
    fun i => rate_bounds (hp i).1 (hp i).2
  rw [countMass_mixture, countMass_mixture]
  calc
    _ ≤ ∑ selector : I → Bool, BernoulliProduct.weight (fun i => rate (p i)) selector *
        (2 / (((BoolCounting.trueSet selector).card : ℝ) + 1)) :=
      BernoulliSmoothing.shifted_mixture_adjacent _
        (BernoulliProduct.weight_nonnegative _ hr) _ _ k
    _ = 2 * (∑ selector : I → Bool, BernoulliProduct.weight (fun i => rate (p i)) selector *
        (BernoulliProduct.count selector + 1)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro selector _
      rw [BoolCounting.count_eq_card]
      simp only [div_eq_mul_inv]
      ring
    _ ≤ 2 * (1 / (∑ i, rate (p i))) :=
      mul_le_mul_of_nonneg_left (BernoulliProduct.reciprocal_moment_bound _ hr hmean) (by norm_num)
    _ = _ := by ring

/-- A self-contained smoothing bound for a sum of independent Bernoullis:
adjacent point masses differ by at most the reciprocal of the variance. -/
theorem countMass_adjacent_variance (p : I → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hvar : 0 < ∑ i, p i * (1 - p i)) (k : ℤ) :
    |countMass p (k + 1) - countMass p k| ≤ 1 / (∑ i, p i * (1 - p i)) := by
  have hrate : 2 * (∑ i, p i * (1 - p i)) ≤ ∑ i, rate (p i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa [mul_assoc] using rate_ge_variance (p i)
  have hmean : 0 < ∑ i, rate (p i) := by linarith
  apply (countMass_adjacent_rate p hp hmean k).trans
  apply (div_le_div_iff₀ hmean hvar).2
  simpa using hrate

theorem weight_half (x : I → Bool) :
    BernoulliProduct.weight (fun _ : I => (1 : ℝ) / 2) x =
      (1 : ℝ) / 2 ^ Fintype.card I := by
  unfold BernoulliProduct.weight
  have heq : ∀ i, (if x i then (1 : ℝ) / 2 else 1 - 1 / 2) = 1 / 2 := by
    intro i
    cases x i <;> norm_num
  simp_rw [heq]
  simp

theorem countMass_half (k : ℤ) :
    countMass (fun _ : I => (1 : ℝ) / 2) k =
      BernoulliSmoothing.fairBinomialMassInt (Fintype.card I) k := by
  simp only [countMass, weight_half]
  exact BoolCounting.fair_count_mass_int k

end QueryComplexity.BernoulliMixture
