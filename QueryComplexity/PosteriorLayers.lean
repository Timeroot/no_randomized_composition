import QueryComplexity.PosteriorMajority

open scoped BigOperators

namespace QueryComplexity.PosteriorMajority

open BernoulliMixture

variable {I Transcript : Type*} [Fintype I] [DecidableEq I] [Fintype Transcript]

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
  have hs := binary_success_le_l1 _ _ hmass₀ hmass₁ answer
  linarith

end QueryComplexity.PosteriorMajority
