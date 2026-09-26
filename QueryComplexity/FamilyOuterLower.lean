import QueryComplexity.OuterLower

namespace QueryComplexity.Construction

theorem scale_ge_ten (n : ℕ) : 10 ≤ scale n := by
  have h : 1 ≤ 2 ^ (2 ^ n) := Nat.one_le_pow _ _ (by omega)
  unfold scale
  omega

theorem pointerArity_ge_three (n : ℕ) : 3 ≤ pointerArity n := by
  have hs : 2 ≤ scale n := (by omega : 2 ≤ 10).trans (scale_ge_ten n)
  have hp : 4 ≤ 2 ^ scale n := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hs
  unfold pointerArity
  omega

theorem pointerArity_le_pow_scale (n : ℕ) : pointerArity n ≤ 2 ^ scale n := Nat.sub_le _ _

/-- Explicit lower bound for the actual reindexed total outer family. -/
theorem R_F_gt (n : ℕ) :
    25 * scale n * (seedLength (pointerArity n) * seedLength (pointerArity n) * pointerArity n ^ 3)
      < R (F n) := by
  rw [F, R_toFin]
  exact R_outer_gt (pointerArity n) (scale n)
    ((by omega : 2 ≤ 3).trans (pointerArity_ge_three n))
    ((by omega : 1 ≤ 10).trans (scale_ge_ten n)) (pointerArity_le_pow_scale n)

theorem R_F_lower (n : ℕ) :
    25 * scale n * (seedLength (pointerArity n) * seedLength (pointerArity n) * pointerArity n ^ 3)
      ≤ R (F n) := (R_F_gt n).le

end QueryComplexity.Construction
