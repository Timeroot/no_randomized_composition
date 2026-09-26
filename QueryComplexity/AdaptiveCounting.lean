import QueryComplexity.FiniteProbability
import Mathlib.Tactic

/-! Exponential tails for adaptively discovered events on an actual finite
sample space. Conditional hazards are stated as finite fiber-mass inequalities. -/

namespace QueryComplexity.AdaptiveCounting

open scoped BigOperators
open FiniteProbability

variable {X State : Type*} [Fintype X] [Fintype State]

omit [Fintype State] in
theorem marked_fiber_identity (μ : X → ℝ) (state : X → State) (marked : X → Bool) (s : State) :
    pushforward (fun x => μ x * (2 : ℝ) ^ (if marked x then 1 else 0)) state s =
      pushforward μ state s + pushforward (fun x => if marked x then μ x else 0) state s := by
  classical
  simp only [pushforward, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> norm_num <;> ring

theorem one_step_moment (μ : X → ℝ) (state : X → State) (count : State → ℕ)
    (marked : X → Bool) (p : ℝ)
    (hhazard : ∀ s, pushforward (fun x => if marked x then μ x else 0) state s ≤
      p * pushforward μ state s) :
    (∑ x, μ x * (2 : ℝ) ^ (count (state x) + if marked x then 1 else 0)) ≤
      (1 + p) * (∑ x, μ x * (2 : ℝ) ^ count (state x)) := by
  have hfactor : ∀ s,
      pushforward (fun x => μ x * (2 : ℝ) ^ (if marked x then 1 else 0)) state s ≤
        (1 + p) * pushforward μ state s := by
    intro s
    rw [marked_fiber_identity]
    have h := hhazard s
    nlinarith
  calc
    _ = ∑ x, (μ x * (2 : ℝ) ^ (if marked x then 1 else 0)) * (2 : ℝ) ^ count (state x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [pow_add]
      ring
    _ = ∑ s, pushforward (fun x => μ x * (2 : ℝ) ^ (if marked x then 1 else 0)) state s *
        (2 : ℝ) ^ count s :=
      (sum_pushforward_mul (fun x => μ x * (2 : ℝ) ^ (if marked x then 1 else 0))
        state (fun s => (2 : ℝ) ^ count s)).symm
    _ ≤ ∑ s, ((1 + p) * pushforward μ state s) * (2 : ℝ) ^ count s :=
      Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_right (hfactor s) (by positivity))
    _ = (1 + p) * ∑ s, pushforward μ state s * (2 : ℝ) ^ count s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := by rw [sum_pushforward_mul]

/-- Counts measurable from the current transcript obey the usual binomial
exponential-moment bound whenever each next conditional hazard is at most `p`. -/
theorem adaptive_moment_bound (μ : X → ℝ) (hmass : ∑ x, μ x = 1)
    (state : ℕ → X → State) (count : ℕ → State → ℕ) (marked : ℕ → X → Bool)
    (p : ℝ) (hp : 0 ≤ p)
    (hzero : ∀ x, count 0 (state 0 x) = 0)
    (hstep : ∀ n x, count (n + 1) (state (n + 1) x) =
      count n (state n x) + if marked n x then 1 else 0)
    (hhazard : ∀ n s, pushforward (fun x => if marked n x then μ x else 0) (state n) s ≤
      p * pushforward μ (state n) s) :
    ∀ n, (∑ x, μ x * (2 : ℝ) ^ count n (state n x)) ≤ (1 + p) ^ n := by
  intro n
  induction n with
  | zero => simp [hzero, hmass]
  | succ n ih =>
    simp_rw [hstep]
    apply (one_step_moment μ (state n) (count n) (marked n) p (hhazard n)).trans
    calc
      _ ≤ (1 + p) * (1 + p) ^ n := mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (1 + p) ^ (n + 1) := by rw [pow_succ]; ring

theorem count_tail_le_moment (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (count : X → ℕ) (h : ℕ) :
    (∑ x, if h ≤ count x then μ x else 0) ≤
      (∑ x, μ x * (2 : ℝ) ^ count x) / (2 : ℝ) ^ h := by
  apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ h)).2
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : h ≤ count x
  · rw [if_pos hx]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hx) (hμ x)
  · rw [if_neg hx, zero_mul]
    exact mul_nonneg (hμ x) (by positivity)

theorem adaptive_tail_bound (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hmass : ∑ x, μ x = 1)
    (state : ℕ → X → State) (count : ℕ → State → ℕ) (marked : ℕ → X → Bool)
    (p : ℝ) (hp : 0 ≤ p)
    (hzero : ∀ x, count 0 (state 0 x) = 0)
    (hstep : ∀ n x, count (n + 1) (state (n + 1) x) =
      count n (state n x) + if marked n x then 1 else 0)
    (hhazard : ∀ n s, pushforward (fun x => if marked n x then μ x else 0) (state n) s ≤
      p * pushforward μ (state n) s)
    (n h : ℕ) :
    (∑ x, if h ≤ count n (state n x) then μ x else 0) ≤ (1 + p) ^ n / (2 : ℝ) ^ h :=
  (count_tail_le_moment μ hμ (fun x => count n (state n x)) h).trans
    (div_le_div_of_nonneg_right
      (adaptive_moment_bound μ hmass state count marked p hp hzero hstep hhazard n) (by positivity))

end QueryComplexity.AdaptiveCounting
