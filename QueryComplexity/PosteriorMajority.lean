import QueryComplexity.BernoulliMixture

/-!
# From product posteriors to indistinguishable adjacent majority layers

All hypotheses about a transcript distribution are explicit. In particular,
this file does not assume that pointer-query transcripts satisfy them.
-/

namespace QueryComplexity.PosteriorMajority

open scoped BigOperators
open BernoulliMixture

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem countMass_nonnegative (p : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (k : ℤ) :
    0 ≤ countMass p k := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact BernoulliProduct.weight_nonnegative p hp x
  · exact le_refl 0

theorem countMass_le_one (p : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (k : ℤ) :
    countMass p k ≤ 1 := by
  rw [← BernoulliProduct.weight_mass p]
  apply Finset.sum_le_sum
  intro x _
  split_ifs
  · exact le_refl _
  · exact BernoulliProduct.weight_nonnegative p hp x

theorem countMass_difference_le_one (p : I → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (k l : ℤ) :
    |countMass p k - countMass p l| ≤ 1 := by
  rw [abs_le]
  have hk0 := countMass_nonnegative p hp k
  have hl0 := countMass_nonnegative p hp l
  have hk1 := countMass_le_one p hp k
  have hl1 := countMass_le_one p hp l
  constructor <;> linarith

noncomputable def variance (p : I → ℝ) : ℝ := ∑ i, p i * (1 - p i)

variable {Transcript : Type*} [Fintype Transcript]

/-- Bayes' formula for the transcript law conditional on a fixed label count. -/
noncomputable def conditionedCountWeight (ν : Transcript → ℝ)
    (p : Transcript → I → ℝ) (prior : ℝ) (k : ℤ) : Transcript → ℝ :=
  fun t => ν t * countMass (p t) k / prior

theorem conditionedCountWeight_mass (ν : Transcript → ℝ)
    (p : Transcript → I → ℝ) (prior : ℝ) (hprior : prior ≠ 0) (k : ℤ)
    (haverage : ∑ t, ν t * countMass (p t) k = prior) :
    ∑ t, conditionedCountWeight ν p prior k t = 1 := by
  simp only [conditionedCountWeight, ← Finset.sum_div]
  rw [haverage, div_self hprior]

theorem weighted_posterior_difference_bound (ν : Transcript → ℝ)
    (hν : ∀ t, 0 ≤ ν t) (hmass : ∑ t, ν t = 1)
    (p : Transcript → I → ℝ) (hp : ∀ t i, 0 ≤ p t i ∧ p t i ≤ 1)
    (good : Transcript → Prop) [DecidablePred good]
    (v δ : ℝ) (hv : 0 < v)
    (hvariance : ∀ t, good t → v ≤ variance (p t))
    (hbad : (∑ t, if good t then 0 else ν t) ≤ δ) (k : ℤ) :
    (∑ t, ν t * |countMass (p t) (k + 1) - countMass (p t) k|) ≤ 1 / v + δ := by
  have hpoint : ∀ t,
      |countMass (p t) (k + 1) - countMass (p t) k| ≤ 1 / v + if good t then 0 else 1 := by
    intro t
    by_cases ht : good t
    · rw [if_pos ht, add_zero]
      have hvar : 0 < variance (p t) := lt_of_lt_of_le hv (hvariance t ht)
      apply (countMass_adjacent_variance (p t) (hp t) hvar k).trans
      exact one_div_le_one_div_of_le hv (hvariance t ht)
    · rw [if_neg ht]
      have h := countMass_difference_le_one (p t) (hp t) (k + 1) k
      have hnonneg : 0 ≤ 1 / v := le_of_lt (one_div_pos.mpr hv)
      linarith
  calc
    _ ≤ ∑ t, ν t * (1 / v + if good t then 0 else 1) :=
      Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (hpoint t) (hν t))
    _ = 1 / v + ∑ t, if good t then 0 else ν t := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hmass, one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      split_ifs <;> simp
    _ ≤ _ := add_le_add (le_refl _) hbad

/-- High posterior variance outside a small exceptional event makes adjacent
count-conditioned transcript laws close in total variation (twice TV here). -/
theorem conditioned_l1_bound (ν : Transcript → ℝ)
    (hν : ∀ t, 0 ≤ ν t) (hmass : ∑ t, ν t = 1)
    (p : Transcript → I → ℝ) (hp : ∀ t i, 0 ≤ p t i ∧ p t i ≤ 1)
    (good : Transcript → Prop) [DecidablePred good]
    (v δ prior : ℝ) (hv : 0 < v) (hprior : 0 < prior)
    (hvariance : ∀ t, good t → v ≤ variance (p t))
    (hbad : (∑ t, if good t then 0 else ν t) ≤ δ) (k : ℤ) :
    (∑ t, |conditionedCountWeight ν p prior (k + 1) t -
      conditionedCountWeight ν p prior k t|) ≤ (1 / v + δ) / prior := by
  have heq : (∑ t, |conditionedCountWeight ν p prior (k + 1) t -
      conditionedCountWeight ν p prior k t|) =
      (∑ t, ν t * |countMass (p t) (k + 1) - countMass (p t) k|) / prior := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro t _
    simp only [conditionedCountWeight, ← sub_div, ← mul_sub, abs_div, abs_mul,
      abs_of_nonneg (hν t), abs_of_pos hprior]
  rw [heq]
  exact div_le_div_of_nonneg_right
    (weighted_posterior_difference_bound ν hν hmass p hp good v δ hv hvariance hbad k)
    hprior.le

/-- The optimal equal-prior binary decision advantage is bounded by one
quarter of the L1 distance. This applies to any deterministic transcript rule. -/
theorem binary_success_le_l1 (μ₀ μ₁ : Transcript → ℝ)
    (hmass₀ : ∑ t, μ₀ t = 1) (hmass₁ : ∑ t, μ₁ t = 1)
    (answer : Transcript → Bool) :
    (1 : ℝ) / 2 * (∑ t, if answer t then μ₁ t else μ₀ t) ≤
      1 / 2 + 1 / 4 * ∑ t, |μ₁ t - μ₀ t| := by
  have hpoint : ∀ t, (if answer t then μ₁ t else μ₀ t) ≤
      (μ₀ t + μ₁ t + |μ₁ t - μ₀ t|) / 2 := by
    intro t
    have h₁ := le_abs_self (μ₁ t - μ₀ t)
    have h₀ := neg_le_abs (μ₁ t - μ₀ t)
    cases answer t <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  have hsum := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset Transcript)) => hpoint t)
  simp only [← Finset.sum_div, Finset.sum_add_distrib, hmass₀, hmass₁] at hsum
  linarith

end QueryComplexity.PosteriorMajority
