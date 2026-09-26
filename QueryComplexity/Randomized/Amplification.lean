import QueryComplexity.Randomized.Algorithm

/-! Explicit iterated-majority amplification, with error and depth bounds. -/

open scoped BigOperators

namespace QueryComplexity

universe u v w

namespace FiniteRandomizedTree

variable {Seed : Type u} [Fintype Seed] {T : Type v} {Output : Type w}

/-- Majority vote among three independent executions. -/
def majority3 (algorithm : FiniteRandomizedTree Seed T Bool) :
    FiniteRandomizedTree (Seed × (Seed × Seed)) T Bool :=
  (algorithm.pair (algorithm.pair algorithm)).mapOutput
    (fun b => (b.1 && b.2.1) || (b.1 && b.2.2) || (b.2.1 && b.2.2))

theorem depthBound_majority3 (algorithm : FiniteRandomizedTree Seed T Bool)
    {d : ℕ} (h : algorithm.DepthBound d) : algorithm.majority3.DepthBound (3 * d) := by
  have hp := algorithm.depthBound_pair (algorithm.pair algorithm) h
    (algorithm.depthBound_pair algorithm h h)
  simpa [majority3, show d + (d + d) = 3 * d by omega] using hp

/-- The exact majority-of-three error polynomial. -/
theorem probability_majority3_error (algorithm : FiniteRandomizedTree Seed T Bool)
    (answer : Bool) (x : T → Bool) :
    algorithm.majority3.probability (fun b => b ≠ answer) x =
      3 * (algorithm.probability (fun b => b ≠ answer) x) ^ 2 -
        2 * (algorithm.probability (fun b => b ≠ answer) x) ^ 3 := by
  classical
  let p : Bool → Prop := fun b => b ≠ answer
  let triple := algorithm.pair (algorithm.pair algorithm)
  let e₀ : Bool × (Bool × Bool) → Prop := fun b => p b.1 ∧ (p b.2.1 ∧ True)
  let e₁ : Bool × (Bool × Bool) → Prop := fun b => p b.1 ∧ (¬ p b.2.1 ∧ p b.2.2)
  let e₂ : Bool × (Bool × Bool) → Prop := fun b => ¬ p b.1 ∧ (p b.2.1 ∧ p b.2.2)
  have hsplit : (fun b : Bool × (Bool × Bool) =>
      ((b.1 && b.2.1) || (b.1 && b.2.2) || (b.2.1 && b.2.2)) ≠ answer) =
      (fun b => e₀ b ∨ (e₁ b ∨ e₂ b)) := by
    funext b
    rcases b with ⟨a, b, c⟩
    cases a <;> cases b <;> cases c <;> cases answer <;> decide
  have hd₀ : ∀ b, ¬ (e₀ b ∧ (e₁ b ∨ e₂ b)) := by simp [e₀, e₁, e₂]; tauto
  have hd₁ : ∀ b, ¬ (e₁ b ∧ e₂ b) := by simp [e₁, e₂]; tauto
  have h₀ : triple.probability e₀ x =
      algorithm.probability p x * algorithm.probability p x := by
    rw [show triple.probability e₀ x = algorithm.probability p x *
      (algorithm.pair algorithm).probability (fun b => p b.1 ∧ True) x from
        algorithm.probability_pair (algorithm.pair algorithm) p (fun b => p b.1 ∧ True) x]
    rw [algorithm.probability_pair algorithm p (fun _ => True) x, probability_true, mul_one]
  have h₁ : triple.probability e₁ x =
      algorithm.probability p x * ((1 - algorithm.probability p x) *
        algorithm.probability p x) := by
    rw [show triple.probability e₁ x = algorithm.probability p x *
      (algorithm.pair algorithm).probability (fun b => ¬ p b.1 ∧ p b.2) x from
        algorithm.probability_pair (algorithm.pair algorithm) p (fun b => ¬ p b.1 ∧ p b.2) x]
    rw [algorithm.probability_pair algorithm (fun b => ¬ p b) p x,
      algorithm.probability_not p x]
  have h₂ : triple.probability e₂ x =
      (1 - algorithm.probability p x) * (algorithm.probability p x *
        algorithm.probability p x) := by
    rw [show triple.probability e₂ x = algorithm.probability (fun b => ¬ p b) x *
      (algorithm.pair algorithm).probability (fun b => p b.1 ∧ p b.2) x from
        algorithm.probability_pair (algorithm.pair algorithm) (fun b => ¬ p b)
          (fun b => p b.1 ∧ p b.2) x]
    rw [algorithm.probability_pair algorithm p p x, algorithm.probability_not p x]
  rw [majority3, probability_mapOutput, hsplit,
    probability_or_of_disjoint triple e₀ (fun b => e₁ b ∨ e₂ b) hd₀,
    probability_or_of_disjoint triple e₁ e₂ hd₁]
  rw [h₀, h₁, h₂]
  dsimp [p]
  ring

/-- A convenient quadratic upper bound for amplification. -/
theorem probability_majority3_error_le (algorithm : FiniteRandomizedTree Seed T Bool)
    (answer : Bool) (x : T → Bool) {ε : ℝ}
    (hε : 0 ≤ ε) (herror : algorithm.probability (fun b => b ≠ answer) x ≤ ε) :
    algorithm.majority3.probability (fun b => b ≠ answer) x ≤ 3 * ε ^ 2 := by
  have hp := algorithm.probability_nonneg (fun b => b ≠ answer) x
  have hp3 : 0 ≤ algorithm.probability (fun b => b ≠ answer) x ^ 3 := pow_nonneg hp _
  rw [probability_majority3_error]
  nlinarith [sq_le_sq₀ hp hε |>.2 herror]

theorem probability_majority3_error_le_polynomial
    (algorithm : FiniteRandomizedTree Seed T Bool) (answer : Bool) (x : T → Bool) {ε : ℝ}
    (hε : 0 ≤ ε) (hhalf : ε ≤ 1 / 2)
    (herror : algorithm.probability (fun b => b ≠ answer) x ≤ ε) :
    algorithm.majority3.probability (fun b => b ≠ answer) x ≤ 3 * ε ^ 2 - 2 * ε ^ 3 := by
  let p := algorithm.probability (fun b => b ≠ answer) x
  have hp : 0 ≤ p := algorithm.probability_nonneg _ _
  have hpe : p ≤ ε := herror
  have hpHalf : p ≤ 1 / 2 := hpe.trans hhalf
  have hεsq := mul_nonneg hε (sub_nonneg.mpr hhalf)
  have hpsq := mul_nonneg hp (sub_nonneg.mpr hpHalf)
  have hεp := mul_nonneg hε (sub_nonneg.mpr hpHalf)
  have hbracket : 0 ≤ 3 * (ε + p) - 2 * (ε ^ 2 + ε * p + p ^ 2) := by
    nlinarith
  have hfactor := mul_nonneg (sub_nonneg.mpr hpe) hbracket
  rw [probability_majority3_error]
  dsimp only [p] at hfactor
  nlinarith

/-- Three constant-size majority stages reduce error `1/3` to at most `1/6`. -/
theorem probability_majority3_three_error (algorithm : FiniteRandomizedTree Seed T Bool)
    (answer : Bool) (x : T → Bool)
    (herror : algorithm.probability (fun b => b ≠ answer) x ≤ 1 / 3) :
    algorithm.majority3.majority3.majority3.probability (fun b => b ≠ answer) x ≤ 1 / 6 := by
  have h₁ : algorithm.majority3.probability (fun b => b ≠ answer) x ≤ 7 / 27 := by
    have h := algorithm.probability_majority3_error_le_polynomial answer x
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num) herror
    norm_num at h ⊢
    exact h
  have h₂ : algorithm.majority3.majority3.probability (fun b => b ≠ answer) x ≤ 1 / 5 := by
    have h := algorithm.majority3.probability_majority3_error_le_polynomial answer x
      (by norm_num : (0 : ℝ) ≤ 7 / 27) (by norm_num) h₁
    linarith
  have h₃ := algorithm.majority3.majority3.probability_majority3_error_le_polynomial answer x
    (by norm_num : (0 : ℝ) ≤ 1 / 5) (by norm_num) h₂
  linarith

/-- Seeds for iterated independent majority stages. -/
def MajoritySeed (Seed : Type u) : ℕ → Type u
  | 0 => Seed
  | n + 1 => MajoritySeed Seed n × (MajoritySeed Seed n × MajoritySeed Seed n)

instance instFintypeMajoritySeed (Seed : Type u) [Fintype Seed] (n : ℕ) :
    Fintype (MajoritySeed Seed n) :=
  match n with
  | 0 => inferInstanceAs (Fintype Seed)
  | n + 1 => by
      letI : Fintype (MajoritySeed Seed n) := instFintypeMajoritySeed Seed n
      exact inferInstanceAs (Fintype (MajoritySeed Seed n ×
        (MajoritySeed Seed n × MajoritySeed Seed n)))

/-- An actual finite distribution on trees for every number of majority stages. -/
def iterateMajority3 (algorithm : FiniteRandomizedTree Seed T Bool) (n : ℕ) :
    FiniteRandomizedTree (MajoritySeed Seed n) T Bool :=
  match n with
  | 0 => algorithm
  | n + 1 => (iterateMajority3 algorithm n).majority3

theorem depthBound_iterateMajority3 (algorithm : FiniteRandomizedTree Seed T Bool)
    {d : ℕ} (hdepth : algorithm.DepthBound d) (n : ℕ) :
    (algorithm.iterateMajority3 n).DepthBound (3 ^ n * d) := by
  induction n with
  | zero => simpa [iterateMajority3] using hdepth
  | succ n ih =>
      have h := (algorithm.iterateMajority3 n).depthBound_majority3 ih
      simpa [iterateMajority3, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- Quadratic error decay at each stage gives a double-exponential error bound,
while the depth grows by `3^n`. -/
theorem probability_iterateMajority3_error
    (algorithm : FiniteRandomizedTree Seed T Bool) (answer : Bool) (x : T → Bool)
    (herror : algorithm.probability (fun b => b ≠ answer) x ≤ 1 / 6) (n : ℕ) :
    (algorithm.iterateMajority3 n).probability (fun b => b ≠ answer) x ≤
      (1 / 3 : ℝ) * (1 / 2 : ℝ) ^ (2 ^ n) := by
  induction n with
  | zero =>
      simpa only [iterateMajority3, pow_zero, pow_one,
        show (1 / 3 : ℝ) * (1 / 2) = 1 / 6 by norm_num] using herror
  | succ n ih =>
      rw [iterateMajority3]
      calc
        _ ≤ 3 * ((1 / 3 : ℝ) * (1 / 2 : ℝ) ^ (2 ^ n)) ^ 2 :=
          (algorithm.iterateMajority3 n).probability_majority3_error_le answer x (by positivity) ih
        _ = (1 / 3 : ℝ) * (1 / 2 : ℝ) ^ (2 ^ (n + 1)) := by
          rw [pow_succ (2 : ℕ) n, pow_mul]
          ring

/-- Amplification starting from the standard `1/3` error guarantee. -/
def amplify (algorithm : FiniteRandomizedTree Seed T Bool) (n : ℕ) :
    FiniteRandomizedTree (MajoritySeed (MajoritySeed Seed 3) n) T Bool :=
  (algorithm.iterateMajority3 3).iterateMajority3 n

theorem depthBound_amplify (algorithm : FiniteRandomizedTree Seed T Bool)
    {d : ℕ} (hdepth : algorithm.DepthBound d) (n : ℕ) :
    (algorithm.amplify n).DepthBound (27 * 3 ^ n * d) := by
  have h := (algorithm.iterateMajority3 3).depthBound_iterateMajority3
    (algorithm.depthBound_iterateMajority3 hdepth 3) n
  simpa [amplify, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem probability_amplify_error (algorithm : FiniteRandomizedTree Seed T Bool)
    (answer : Bool) (x : T → Bool)
    (herror : algorithm.probability (fun b => b ≠ answer) x ≤ 1 / 3) (n : ℕ) :
    (algorithm.amplify n).probability (fun b => b ≠ answer) x ≤
      (1 / 3 : ℝ) * (1 / 2 : ℝ) ^ (2 ^ n) := by
  apply probability_iterateMajority3_error
  exact algorithm.probability_majority3_three_error answer x herror

end FiniteRandomizedTree
end QueryComplexity
