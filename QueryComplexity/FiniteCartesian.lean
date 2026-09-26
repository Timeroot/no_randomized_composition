import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic

namespace QueryComplexity.FiniteCartesian

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (β : I → Type*) [∀ i, Fintype (β i)]

def piFiberEquiv (i : I) (b : β i) :
    {f : ∀ j, β j // f i = b} ≃ (∀ j : {j // j ≠ i}, β j) where
  toFun f j := f.1 j
  invFun f := ⟨(Equiv.piSplitAt i β).symm (b, f), by simp [Equiv.piSplitAt]⟩
  left_inv f := by
    ext j
    by_cases hj : j = i
    · subst j; simpa [Equiv.piSplitAt] using f.2.symm
    · simp [Equiv.piSplitAt, hj]
  right_inv f := by
    funext j
    simp [Equiv.piSplitAt, j.2]

theorem pi_fiber_card_mul (i : I) (b : β i) :
    Nat.card {f : ∀ j, β j // f i = b} * Nat.card (β i) = Nat.card (∀ j, β j) := by
  rw [Nat.card_congr (piFiberEquiv β i b), Nat.card_congr (Equiv.piSplitAt i β), Nat.card_prod]
  exact Nat.mul_comm _ _

theorem pi_fiber_probability [∀ i, Nonempty (β i)] (i : I) (b : β i) :
    (Nat.card {f : ∀ j, β j // f i = b} : ℝ) / (Nat.card (∀ j, β j) : ℝ) =
      1 / (Nat.card (β i) : ℝ) := by
  have htotal : (Nat.card (∀ j, β j) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hlocal : (Nat.card (β i) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  apply (div_eq_div_iff htotal hlocal).2
  simpa using congrArg (fun n : ℕ => (n : ℝ)) (pi_fiber_card_mul β i b)

end QueryComplexity.FiniteCartesian
