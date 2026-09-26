import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

open scoped BigOperators

namespace QueryComplexity

def resampleSwap {I T : Type*} [DecidableEq I] (i : I) :
    ((I → T) × T) ≃ ((I → T) × T) where
  toFun p := (Function.update p.1 i p.2, p.1 i)
  invFun p := (Function.update p.1 i p.2, p.1 i)
  left_inv p := by
    ext j
    · by_cases hj : j = i <;> simp [hj]
    · simp
  right_inv p := by
    ext j
    · by_cases hj : j = i <;> simp [hj]
    · simp

theorem sum_resample {I T : Type*} [Fintype I] [DecidableEq I] [Fintype T]
    (i : I) (f : (I → T) → ℕ) :
    (∑ a : I → T, ∑ t : T, f (Function.update a i t)) =
      Fintype.card T * ∑ a : I → T, f a := by
  classical
  have h := (resampleSwap (T := T) i).sum_comp (fun p : (I → T) × T => f p.1)
  simpa [resampleSwap, Fintype.sum_prod_type, Finset.mul_sum, mul_comm] using h

theorem sum_resample_real {I T : Type*} [Fintype I] [DecidableEq I] [Fintype T]
    (i : I) (f : (I → T) → ℝ) :
    (∑ a : I → T, ∑ t : T, f (Function.update a i t)) =
      (Fintype.card T : ℝ) * ∑ a : I → T, f a := by
  classical
  have h := (resampleSwap (T := T) i).sum_comp (fun p : (I → T) × T => f p.1)
  simpa [resampleSwap, Fintype.sum_prod_type, Finset.mul_sum, mul_comm] using h

end QueryComplexity
