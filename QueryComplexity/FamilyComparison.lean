import QueryComplexity.FamilyAsymptotics
import QueryComplexity.FamilyUpper

open Filter Asymptotics

namespace QueryComplexity.Construction

theorem pointerArity_odd (n : ℕ) : Odd (pointerArity n) := by
  have hs : scale n ≠ 0 := by have := scale_ge_ten n; omega
  have hp : Even (2 ^ scale n) := (show Even (2 : ℕ) by decide).pow_of_ne_zero hs
  apply (Nat.odd_sub' (Nat.one_le_pow _ _ (by omega))).mpr
  simpa using hp

theorem totalComposedCost_le (n : ℕ) :
    totalComposedCost (pointerArity n) (copies n) (n + 4) ≤
      10 ^ 18 * scale n * 3 ^ (n + 4) * seedLength (pointerArity n) ^ 2 *
        pointerArity n ^ 5 * pointerPayloadWidth (pointerArity n) := by
  have h := raw_composition_cost_bound (pointerArity n) (seedLength (pointerArity n))
    (scale n) (n + 4) (pointerPayloadWidth (pointerArity n))
    ((by omega : 1 ≤ 3).trans (pointerArity_ge_three n)) (seedLength_pos _)
    ((by omega : 1 ≤ 10).trans (scale_ge_ten n))
  convert h using 1 <;>
    simp only [totalComposedCost, composedCoreCost, composedSeedCost, outerVerifierCost,
      cellWidth, copies, payloadWidth, ApproxIndex.seedSize] <;> ring

/-- The composed functions' upper bound, with all algorithms and error bounds
instantiated and no complexity assumptions. -/
theorem R_composition_upper (n : ℕ) :
    R (comp (F n) (G n)) ≤
      10 ^ 18 * scale n * 3 ^ (n + 4) * seedLength (pointerArity n) ^ 2 *
        pointerArity n ^ 5 * pointerPayloadWidth (pointerArity n) := by
  rw [F, G, R_comp_toFin]
  exact (R_comp_le_totalComposedCost (pointerArity n) (copies n)
    (pointerArity_ge_three n) (pointerArity_odd n) (n + 4)
    ((copies_amplification_error n).trans (by norm_num))).trans (totalComposedCost_le n)

/-- Only the inner lower bound remains as a premise in this quantitative
comparison; the outer lower and composed upper are proved for the actual family. -/
theorem composition_rate_of_inner_lower (n : ℕ)
    (hG : (pointerPayloadWidth (pointerArity n) : ℝ) * (pointerArity n : ℝ) ^ 2 *
      (scale n : ℝ) / 1000000 ≤ (R (G n) : ℝ)) :
    (R (comp (F n) (G n)) : ℝ) ≤
      (40000 * (10 : ℝ) ^ 18 * 3 ^ (n + 4) / scale n) *
        ((R (F n) : ℝ) * (R (G n) : ℝ)) := by
  have hF : 25 * (scale n : ℝ) * (seedLength (pointerArity n) : ℝ) ^ 2 *
      (pointerArity n : ℝ) ^ 3 ≤ (R (F n) : ℝ) := by
    have h := R_F_lower n
    exact_mod_cast (by simpa only [pow_two, Nat.mul_assoc] using h)
  have hupper : (R (comp (F n) (G n)) : ℝ) ≤
      10 ^ 18 * (scale n : ℝ) * 3 ^ (n + 4) * (seedLength (pointerArity n) : ℝ) ^ 2 *
        (pointerArity n : ℝ) ^ 5 * (pointerPayloadWidth (pointerArity n) : ℝ) := by
    exact_mod_cast R_composition_upper n
  exact composition_coefficient_bound _ _ _ _ _ _ _ _ _ (by positivity)
    (by exact_mod_cast (show 0 < scale n by have := scale_ge_ten n; omega))
    (by positivity) (by positivity) (by positivity) (by positivity) hF hG hupper

theorem counterexample_of_eventual_inner_lower
    (hG : ∀ᶠ n in atTop,
      (pointerPayloadWidth (pointerArity n) : ℝ) * (pointerArity n : ℝ) ^ 2 *
        (scale n : ℝ) / 1000000 ≤ (R (G n) : ℝ)) : TotalCompositionCounterexample := by
  apply counterexample_of_rate F G (fun n => ⟨F_R_pos n, G_R_pos n⟩)
    (amplification_rate_littleO (40000 * (10 : ℝ) ^ 18) 4)
  filter_upwards [hG] with n hn
  exact composition_rate_of_inner_lower n hn

end QueryComplexity.Construction
