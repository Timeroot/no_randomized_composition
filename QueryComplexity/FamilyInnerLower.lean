import QueryComplexity.PointerCellLower
import QueryComplexity.PointerEncodedLower
import QueryComplexity.FamilyComparison

open Filter

namespace QueryComplexity.Construction

open PointerDistributions PointerLowerNumerics

/-- The concrete encoded inner function has the required linear-in-scale
lower bound, obtained from its explicit hard distribution. -/
theorem R_inner_lower_large_scale (s : ℕ) (hs : 1000 ≤ s) :
    (pointerPayloadWidth (arity s) : ℝ) * (arity s : ℝ) ^ 2 * (s : ℝ) / 1000000 ≤
      (R (inner (arity s)) : ℝ) := by
  have hodd : Odd (arity s) := by
    have hp : Even (2 ^ s) := (show Even (2 : ℕ) by decide).pow_of_ne_zero (by omega)
    apply (Nat.odd_sub' (Nat.one_le_pow _ _ (by omega))).mpr
    simpa using hp
  obtain ⟨m, hm⟩ := hodd
  have hq : arity s = 2 * m + 1 := by omega
  have hcell := R_inner_lower_of_cell_bound m (cellBudget s) (3 / 5) (by norm_num) (by
    intro tree ht
    exact pointer_majority_cell_hard s m hs hq tree ht)
  rw [← hq] at hcell
  exact (encoding_budget_lower s (pointerPayloadWidth (arity s))).trans (by exact_mod_cast hcell)

/-- The eventual inner lower bound consumed by the final comparison theorem. -/
theorem eventually_R_G_lower : ∀ᶠ n in atTop,
    (pointerPayloadWidth (pointerArity n) : ℝ) * (pointerArity n : ℝ) ^ 2 *
      (scale n : ℝ) / 1000000 ≤ (R (G n) : ℝ) := by
  filter_upwards [eventually_scale_ge 1000] with n hn
  have h := R_inner_lower_large_scale (scale n) hn
  rw [G, R_toFin]
  simpa only [arity, pointerArity] using h

end QueryComplexity.Construction
