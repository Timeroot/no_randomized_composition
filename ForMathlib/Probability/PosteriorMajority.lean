import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import ForMathlib.Probability.BernoulliMixture
import ForMathlib.Probability.FiniteProbability

/-! Bernoulli posterior variance and distances between adjacent count layers. -/

section

/-! Algebraic bounds for the Bernoulli posterior associated with a likelihood ratio. -/

namespace BernoulliPosterior

/-- The posterior-variance identity is algebraic, including at `a = -1`. -/
theorem posterior_variance_identity {K : Type*} [Field K] (a : K) :
    (a / (1 + a)) * (1 - a / (1 + a)) = a / (1 + a) ^ 2 := by
  by_cases hden : 1 + a = 0
  · simp [hden]
  field_simp
  ring

theorem posterior_variance_lower (a r : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hr : r ≤ a) :
    r / 4 ≤ (a / (1 + a)) * (1 - a / (1 + a)) := by
  rw [posterior_variance_identity]
  have hden : 0 < (1 + a) ^ 2 := by positivity
  have hsq : (1 + a) ^ 2 ≤ 4 := by nlinarith
  calc
    r / 4 ≤ a / 4 := by grw [hr]
    _ ≤ a / (1 + a) ^ 2 := by grw [hsq]

end BernoulliPosterior

end

section

/-!
# From product posteriors to indistinguishable adjacent majority layers

Weighted bounds on the distance between adjacent count layers of finite
product distributions, expressed through their posterior variances.
-/

namespace PosteriorMajority

open scoped BigOperators
open BernoulliMixture

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem countMass_nonnegative (p : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (k : ℤ) :
    0 ≤ countMass p k := by
  refine Finset.sum_nonneg fun x _ => ?_
  split_ifs
  · exact BernoulliProduct.weight_nonnegative p hp x
  · exact le_refl 0

noncomputable def variance (p : I → ℝ) : ℝ := ∑ i, p i * (1 - p i)

variable {Transcript : Type*} [Fintype Transcript]

/-- Bayes' formula for the transcript law conditional on a fixed label count. -/
noncomputable def conditionedCountWeight (ν : Transcript → ℝ)
    (p : Transcript → I → ℝ) (prior : ℝ) (k : ℤ) : Transcript → ℝ :=
  fun t => ν t * countMass (p t) k / prior

end PosteriorMajority

end

section

open scoped BigOperators

namespace PosteriorMajority

open BernoulliMixture

variable {I Transcript : Type*} [Fintype I] [DecidableEq I] [Fintype Transcript]

omit [Fintype Transcript] in
theorem conditionedCountWeight_nonneg (ν : Transcript → ℝ) (hν : ∀ t, 0 ≤ ν t)
    (p : Transcript → I → ℝ) (hp : ∀ t i, 0 ≤ p t i ∧ p t i ≤ 1)
    (prior : ℝ) (hprior : 0 ≤ prior) (k : ℤ) (t : Transcript) :
    0 ≤ conditionedCountWeight ν p prior k t :=
  div_nonneg (mul_nonneg (hν t) (countMass_nonnegative (p t) (hp t) k)) hprior

/-- The exceptional event is charged under each conditioned layer. Its
probability therefore does not incur an inverse-prior factor. -/
theorem conditioned_l1_bound_layers (ν : Transcript → ℝ)
    (hν : ∀ t, 0 ≤ ν t) (hmass : ∑ t, ν t = 1)
    (p : Transcript → I → ℝ) (hp : ∀ t i, 0 ≤ p t i ∧ p t i ≤ 1)
    (good : Transcript → Prop) [DecidablePred good]
    (v δ₀ δ₁ prior : ℝ) (hv : 0 < v) (hprior : 0 < prior)
    (hvariance : ∀ t, ν t ≠ 0 → good t → v ≤ variance (p t)) (k : ℤ)
    (hbad₀ : (∑ t, if good t then 0 else conditionedCountWeight ν p prior k t) ≤ δ₀)
    (hbad₁ : (∑ t, if good t then 0 else conditionedCountWeight ν p prior (k + 1) t) ≤ δ₁) :
    (∑ t, |conditionedCountWeight ν p prior (k + 1) t -
      conditionedCountWeight ν p prior k t|) ≤ 1 / (v * prior) + δ₀ + δ₁ := by
  have hpoint (t : Transcript) :
      |conditionedCountWeight ν p prior (k + 1) t - conditionedCountWeight ν p prior k t| ≤
        ν t / (v * prior) +
          (if good t then 0 else conditionedCountWeight ν p prior k t) +
          (if good t then 0 else conditionedCountWeight ν p prior (k + 1) t) := by
    by_cases ht : good t
    · simp only [if_pos ht, add_zero]
      by_cases hz : ν t = 0
      · simp [conditionedCountWeight, hz]
      · have hvar : 0 < variance (p t) := hv.trans_le (hvariance t hz ht)
        have hb := (countMass_adjacent_variance (p t) (hp t) hvar k).trans
          (one_div_le_one_div_of_le hv (hvariance t hz ht))
        calc
          _ = ν t * |countMass (p t) (k + 1) - countMass (p t) k| / prior := by
            simp only [conditionedCountWeight, ← sub_div, ← mul_sub, abs_div, abs_mul,
              abs_of_nonneg (hν t), abs_of_pos hprior]
          _ ≤ ν t * (1 / v) / prior :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (hν t)) hprior.le
          _ = ν t / (v * prior) := by ring
    · simp only [if_neg ht]
      have h₀ := conditionedCountWeight_nonneg ν hν p hp prior hprior.le k t
      have h₁ := conditionedCountWeight_nonneg ν hν p hp prior hprior.le (k + 1) t
      have hbase : |conditionedCountWeight ν p prior (k + 1) t -
          conditionedCountWeight ν p prior k t| ≤
          conditionedCountWeight ν p prior k t + conditionedCountWeight ν p prior (k + 1) t := by
        rw [abs_le]
        constructor <;> linarith
      have hn : 0 ≤ ν t / (v * prior) := div_nonneg (hν t) (mul_pos hv hprior).le
      linarith
  have hsum := Finset.sum_le_sum fun t (_ : t ∈ (Finset.univ : Finset Transcript)) => hpoint t
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, hmass] at hsum
  linarith

theorem binary_success_le_layers (ν : Transcript → ℝ)
    (hν : ∀ t, 0 ≤ ν t) (hmass : ∑ t, ν t = 1)
    (p : Transcript → I → ℝ) (hp : ∀ t i, 0 ≤ p t i ∧ p t i ≤ 1)
    (good : Transcript → Prop) [DecidablePred good]
    (v δ₀ δ₁ prior : ℝ) (hv : 0 < v) (hprior : 0 < prior)
    (hvariance : ∀ t, ν t ≠ 0 → good t → v ≤ variance (p t)) (k : ℤ)
    (hbad₀ : (∑ t, if good t then 0 else conditionedCountWeight ν p prior k t) ≤ δ₀)
    (hbad₁ : (∑ t, if good t then 0 else conditionedCountWeight ν p prior (k + 1) t) ≤ δ₁)
    (hmass₀ : ∑ t, conditionedCountWeight ν p prior k t = 1)
    (hmass₁ : ∑ t, conditionedCountWeight ν p prior (k + 1) t = 1)
    (answer : Transcript → Bool) :
    (1 : ℝ) / 2 * (∑ t, if answer t then conditionedCountWeight ν p prior (k + 1) t
      else conditionedCountWeight ν p prior k t) ≤
      1 / 2 + 1 / 4 * (1 / (v * prior) + δ₀ + δ₁) := by
  have hl := conditioned_l1_bound_layers ν hν hmass p hp good v δ₀ δ₁ prior hv hprior
    hvariance k hbad₀ hbad₁
  have hs := FiniteProbability.binary_success_le_l1 _ _ hmass₀ hmass₁ answer
  linarith

end PosteriorMajority

end
