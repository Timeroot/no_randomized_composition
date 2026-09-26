import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! Finite path sums for an adaptive process and an elementary discovery
tail bound. No measure theory or limiting probability space is used. -/

namespace QueryComplexity.FiniteProcess

open scoped BigOperators

universe u

variable {State : Type u} [Fintype State]

def Path (State : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => State × Path State n

instance pathFintype : (n : ℕ) → Fintype (Path State n)
  | 0 => by change Fintype PUnit; infer_instance
  | n + 1 => by
    change Fintype (State × Path State n)
    letI := pathFintype n
    infer_instance

noncomputable def pathWeight (K : State → State → ℝ) :
    (n : ℕ) → State → Path State n → ℝ
  | 0, _, _ => 1
  | n + 1, state, path => K state path.1 * pathWeight K n path.1 path.2

def hits (marked : State → State → Bool) : (n : ℕ) → State → Path State n → ℕ
  | 0, _, _ => 0
  | n + 1, state, path => (if marked state path.1 then 1 else 0) + hits marked n path.1 path.2

omit [Fintype State] in
theorem pathWeight_nonnegative (K : State → State → ℝ) (hK : ∀ s t, 0 ≤ K s t) :
    ∀ n state path, 0 ≤ pathWeight K n state path := by
  intro n
  induction n with
  | zero => intros; exact zero_le_one
  | succ n ih => rintro state ⟨next, path⟩; exact mul_nonneg (hK state next) (ih next path)

theorem pathWeight_mass (K : State → State → ℝ) (hK : ∀ s, ∑ t, K s t = 1) :
    ∀ n state, (∑ path, pathWeight K n state path) = 1 := by
  intro n
  induction n with
  | zero => intro state; simp [pathWeight, Path]
  | succ n ih =>
    intro state
    change (∑ path : State × Path State n, K state path.1 * pathWeight K n path.1 path.2) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ih, mul_one]
    exact hK state

noncomputable def moment (K : State → State → ℝ) (marked : State → State → Bool)
    (n : ℕ) (state : State) : ℝ :=
  ∑ path, pathWeight K n state path * (2 : ℝ) ^ hits marked n state path

theorem moment_zero (K : State → State → ℝ) (marked : State → State → Bool) (state : State) :
    moment K marked 0 state = 1 := by simp [moment, pathWeight, hits, Path]

theorem moment_succ (K : State → State → ℝ) (marked : State → State → Bool)
    (n : ℕ) (state : State) :
    moment K marked (n + 1) state =
      ∑ next, K state next * (if marked state next then (2 : ℝ) else 1) * moment K marked n next := by
  change (∑ path : State × Path State n,
    (K state path.1 * pathWeight K n path.1 path.2) *
      (2 : ℝ) ^ ((if marked state path.1 then 1 else 0) + hits marked n path.1 path.2)) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro next _
  unfold moment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro path _
  cases marked state next <;> simp only [Bool.false_eq_true, ↓reduceIte, pow_add, pow_zero, pow_one] <;> ring

theorem step_factor_bound (K : State → State → ℝ) (marked : State → State → Bool)
    (state : State) (p : ℝ) (hmass : ∑ next, K state next = 1)
    (hhazard : (∑ next, if marked state next then K state next else 0) ≤ p) :
    (∑ next, K state next * (if marked state next then (2 : ℝ) else 1)) ≤ 1 + p := by
  have heq : (∑ next, K state next * (if marked state next then (2 : ℝ) else 1)) =
      (∑ next, K state next) + (∑ next, if marked state next then K state next else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro next _
    cases marked state next <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring
  rw [heq, hmass]
  exact add_le_add (le_refl _) hhazard

/-- Conditional discovery probability at most `p` at every state bounds the
exponential moment after any number of adaptive steps. -/
theorem moment_bound (K : State → State → ℝ) (marked : State → State → Bool)
    (hK : ∀ s t, 0 ≤ K s t) (hmass : ∀ s, ∑ t, K s t = 1)
    (p : ℝ) (hp : 0 ≤ p)
    (hhazard : ∀ s, (∑ t, if marked s t then K s t else 0) ≤ p) :
    ∀ n state, moment K marked n state ≤ (1 + p) ^ n := by
  intro n
  induction n with
  | zero => intro state; rw [moment_zero, pow_zero]
  | succ n ih =>
    intro state
    rw [moment_succ]
    calc
      _ ≤ ∑ next, K state next * (if marked state next then (2 : ℝ) else 1) * (1 + p) ^ n := by
        apply Finset.sum_le_sum
        intro next _
        apply mul_le_mul_of_nonneg_left (ih next)
        exact mul_nonneg (hK state next) (by split_ifs <;> norm_num)
      _ = (∑ next, K state next * (if marked state next then (2 : ℝ) else 1)) * (1 + p) ^ n := by
        rw [Finset.sum_mul]
      _ ≤ (1 + p) * (1 + p) ^ n :=
        mul_le_mul_of_nonneg_right (step_factor_bound K marked state p (hmass state) (hhazard state))
          (pow_nonneg (by linarith) _)
      _ = (1 + p) ^ (n + 1) := by rw [pow_succ]; ring

theorem tail_le_moment (K : State → State → ℝ) (marked : State → State → Bool)
    (hK : ∀ s t, 0 ≤ K s t) (n h : ℕ) (state : State) :
    (∑ path, if h ≤ hits marked n state path then pathWeight K n state path else 0) ≤
      moment K marked n state / (2 : ℝ) ^ h := by
  apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ h)).2
  rw [Finset.sum_mul]
  unfold moment
  apply Finset.sum_le_sum
  intro path _
  by_cases hhit : h ≤ hits marked n state path
  · rw [if_pos hhit]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hhit) (pathWeight_nonnegative K hK n state path)
  · rw [if_neg hhit, zero_mul]
    exact mul_nonneg (pathWeight_nonnegative K hK n state path) (by positivity)

theorem discovery_tail_bound (K : State → State → ℝ) (marked : State → State → Bool)
    (hK : ∀ s t, 0 ≤ K s t) (hmass : ∀ s, ∑ t, K s t = 1)
    (p : ℝ) (hp : 0 ≤ p)
    (hhazard : ∀ s, (∑ t, if marked s t then K s t else 0) ≤ p)
    (n h : ℕ) (state : State) :
    (∑ path, if h ≤ hits marked n state path then pathWeight K n state path else 0) ≤
      (1 + p) ^ n / (2 : ℝ) ^ h :=
  (tail_le_moment K marked hK n h state).trans
    (div_le_div_of_nonneg_right (moment_bound K marked hK hmass p hp hhazard n state) (by positivity))

end QueryComplexity.FiniteProcess
