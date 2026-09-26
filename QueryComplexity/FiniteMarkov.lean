import QueryComplexity.RandomizedPrograms

/-! Finite recurrence bounds for bounded adaptive randomized programs. -/

namespace QueryComplexity.RandomizedOracle

universe u v w

variable {Query : Type u} {State : Type v} {Output : Type w}

theorem value_mem_Icc (p : Query → ℝ) (hp : ∀ q, 0 ≤ p q ∧ p q ≤ 1)
    (step : State → QueryStep Query Bool State Output) (payoff : Output → ℝ)
    (hpayoff : ∀ a, 0 ≤ payoff a ∧ payoff a ≤ 1) (fallback : Output)
    (n : ℕ) (state : State) :
    0 ≤ value p step payoff fallback n state ∧ value p step payoff fallback n state ≤ 1 := by
  induction n generalizing state with
  | zero => exact hpayoff fallback
  | succ n ih =>
      cases hs : step state with
      | done answer => simpa only [value, hs] using hpayoff answer
      | ask query next =>
          simp only [value, hs]
          have hf := ih (next false)
          have ht := ih (next true)
          have hpf : 0 ≤ 1 - p query := sub_nonneg.mpr (hp query).2
          refine ⟨add_nonneg (mul_nonneg hpf hf.1) (mul_nonneg (hp query).1 ht.1), ?_⟩
          calc
            _ ≤ (1 - p query) * 1 + p query * 1 :=
              add_le_add (mul_le_mul_of_nonneg_left hf.2 hpf)
                (mul_le_mul_of_nonneg_left ht.2 (hp query).1)
            _ = 1 := by ring

/-- Finite-horizon supermartingale comparison, expressed entirely as finite
weighted recursion and requiring no stopping-time theorem. -/
theorem value_le_potential (p : Query → ℝ) (hp : ∀ q, 0 ≤ p q ∧ p q ≤ 1)
    (step : State → QueryStep Query Bool State Output) (payoff : Output → ℝ) (fallback : Output)
    (invariant : State → Prop) (potential : State → ℝ)
    (hbase : ∀ state, invariant state → payoff fallback ≤ potential state)
    (hstep : ∀ state, invariant state →
      match step state with
      | .done answer => payoff answer ≤ potential state
      | .ask query next => invariant (next false) ∧ invariant (next true) ∧
          (1 - p query) * potential (next false) + p query * potential (next true) ≤ potential state)
    (n : ℕ) (state : State) (hstate : invariant state) :
    value p step payoff fallback n state ≤ potential state := by
  induction n generalizing state with
  | zero => exact hbase state hstate
  | succ n ih =>
      have hs := hstep state hstate
      cases hquery : step state with
      | done answer => simpa only [value, hquery] using hs
      | ask query next =>
          simp only [hquery] at hs
          simp only [value, hquery]
          exact (add_le_add
            (mul_le_mul_of_nonneg_left (ih _ hs.1) (sub_nonneg.mpr (hp query).2))
            (mul_le_mul_of_nonneg_left (ih _ hs.2.1) (hp query).1)).trans hs.2.2

/-- Simultaneous control of accepting exits and timeout. `H` pays for accepting
exits, and `V` decreases by at least one per call. The fallback accepts. -/
theorem accept_with_cap_le (p : Query → ℝ) (hp : ∀ q, 0 ≤ p q ∧ p q ≤ 1)
    (step : State → QueryStep Query Bool State Bool) (invariant : State → Prop)
    (H V : State → ℝ)
    (hnonneg : ∀ state, invariant state → 0 ≤ H state ∧ 0 ≤ V state)
    (hstep : ∀ state, invariant state →
      match step state with
      | .done answer => (if answer then (1 : ℝ) else 0) ≤ H state
      | .ask query next => invariant (next false) ∧ invariant (next true) ∧ 1 ≤ V state ∧
          (1 - p query) * H (next false) + p query * H (next true) ≤ H state ∧
          (1 - p query) * V (next false) + p query * V (next true) ≤ V state - 1)
    (n : ℕ) (state : State) (hstate : invariant state) :
    value p step (fun b => if b then 1 else 0) true (n + 1) state ≤
      H state + V state / ((n : ℝ) + 1) := by
  induction n generalizing state with
  | zero =>
      have hs := hstep state hstate
      have hn := hnonneg state hstate
      cases hquery : step state with
      | done answer =>
          simp only [hquery] at hs
          simpa only [value, hquery, Nat.cast_zero, zero_add, div_one] using
            hs.trans (le_add_of_nonneg_right hn.2)
      | ask query next =>
          simp only [hquery] at hs
          simp only [value, hquery, Nat.cast_zero, zero_add, div_one, ↓reduceIte]
          nlinarith [hs.2.2.1]
  | succ n ih =>
      have hs := hstep state hstate
      have hn := hnonneg state hstate
      have hd₁ : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hd₂ : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hdenom : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
      rw [hdenom]
      cases hquery : step state with
      | done answer =>
          simp only [hquery] at hs
          simpa only [value, hquery] using
            hs.trans (le_add_of_nonneg_right (div_nonneg hn.2 hd₂.le))
      | ask query next =>
          simp only [hquery] at hs
          by_cases hV : V state ≤ (n : ℝ) + 2
          · simp only [value, hquery]
            have hfrac : (V state - 1) / ((n : ℝ) + 1) ≤ V state / ((n : ℝ) + 2) :=
              (div_le_div_iff₀ hd₁ hd₂).2 (by nlinarith)
            calc
              _ ≤ (1 - p query) * (H (next false) + V (next false) / ((n : ℝ) + 1)) +
                    p query * (H (next true) + V (next true) / ((n : ℝ) + 1)) :=
                add_le_add
                  (mul_le_mul_of_nonneg_left (ih _ hs.1) (sub_nonneg.mpr (hp query).2))
                  (mul_le_mul_of_nonneg_left (ih _ hs.2.1) (hp query).1)
              _ = ((1 - p query) * H (next false) + p query * H (next true)) +
                    ((1 - p query) * V (next false) + p query * V (next true)) / ((n : ℝ) + 1) := by ring
              _ ≤ H state + (V state - 1) / ((n : ℝ) + 1) :=
                add_le_add hs.2.2.2.1 (div_le_div_of_nonneg_right hs.2.2.2.2 hd₁.le)
              _ ≤ H state + V state / ((n : ℝ) + 2) := add_le_add le_rfl hfrac
          · have hprob := (value_mem_Icc p hp step (fun b => if b then 1 else 0)
              (by intro b; cases b <;> norm_num) true (n + 1 + 1) state).2
            have hdiv : 1 ≤ V state / ((n : ℝ) + 2) :=
              (le_div_iff₀ hd₂).2 (by linarith)
            exact hprob.trans (hdiv.trans (le_add_of_nonneg_left hn.1))

end QueryComplexity.RandomizedOracle
