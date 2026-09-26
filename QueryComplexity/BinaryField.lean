import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Data.Fintype.Pi

/-! Boolean coordinates carry their usual two-element field structure.
Addition is XOR and multiplication is AND. -/

namespace QueryComplexity

instance boolNoZeroDivisors : NoZeroDivisors Bool where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b h
    cases a <;> cases b
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · cases h

instance boolIsDomain : IsDomain Bool := NoZeroDivisors.to_isDomain Bool

noncomputable instance boolField : Field Bool := Fintype.fieldOfDomain Bool

theorem bool_zero : (0 : Bool) = false := rfl
theorem bool_one : (1 : Bool) = true := rfl

end QueryComplexity
