import QueryComplexity.Definitions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

/-! The analytic step in the composition argument. All complexity bounds in
these lemmas are explicit hypotheses; none is asserted without a proof. -/

open Filter Asymptotics
open scoped Topology

namespace QueryComplexity

/-- A vanishing multiplicative upper bound implies little-o. -/
theorem littleO_of_eventual_rate {u v e : ℕ → ℝ}
    (he : IsLittleO atTop e (fun _ => (1 : ℝ)))
    (hu : ∀ᶠ n in atTop, ‖u n‖ ≤ e n * ‖v n‖) :
    IsLittleO atTop u v := by
  apply IsLittleO.of_bound
  intro c hc
  filter_upwards [he.bound hc, hu] with n hen hun
  have hen' : e n ≤ c := (le_abs_self _).trans (by simpa using hen)
  exact hun.trans (mul_le_mul_of_nonneg_right hen' (norm_nonneg _))

/-- The logarithmic loss occurring in the construction vanishes. -/
theorem log_div_self_littleO {t : ℕ → ℝ}
    (ht : Tendsto t atTop atTop) :
    IsLittleO atTop (fun n => Real.log (t n) / t n) (fun _ => (1 : ℝ)) := by
  apply (isLittleO_one_iff ℝ).mpr
  exact (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp ht

/-- Translate an actual ratio bound on the randomized complexities to the
analytic conclusion used by the comparator. -/
theorem composition_littleO_of_rate
    {a b : ℕ → ℕ}
    (F : (n : ℕ) → BoolFn (Fin (a n)))
    (G : (n : ℕ) → BoolFn (Fin (b n)))
    {e : ℕ → ℝ}
    (he : IsLittleO atTop e (fun _ => (1 : ℝ)))
    (hbound : ∀ᶠ n in atTop,
      (R (comp (F n) (G n)) : ℝ) ≤
        e n * ((R (F n) : ℝ) * (R (G n) : ℝ))) :
    IsLittleO atTop
      (fun n => (R (comp (F n) (G n)) : ℝ))
      (fun n => (R (F n) : ℝ) * (R (G n) : ℝ)) := by
  apply littleO_of_eventual_rate he
  filter_upwards [hbound] with n hn
  simpa only [Real.norm_eq_abs, Nat.abs_cast, abs_mul] using hn

/-- A sufficient condition, with the required nondegeneracy stated openly. -/
theorem counterexample_of_rate
    {a b : ℕ → ℕ}
    (F : (n : ℕ) → BoolFn (Fin (a n)))
    (G : (n : ℕ) → BoolFn (Fin (b n)))
    (hpos : ∀ n, 0 < R (F n) ∧ 0 < R (G n))
    {e : ℕ → ℝ}
    (he : IsLittleO atTop e (fun _ => (1 : ℝ)))
    (hbound : ∀ᶠ n in atTop,
      (R (comp (F n) (G n)) : ℝ) ≤
        e n * ((R (F n) : ℝ) * (R (G n) : ℝ))) :
    TotalCompositionCounterexample :=
  ⟨a, b, F, G, hpos, composition_littleO_of_rate F G he hbound⟩

end QueryComplexity
