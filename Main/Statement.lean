import QueryComplexity.Basic
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Statement of the total composition counterexample

The target uses the ordinary randomized query model from the reusable
library. Positivity rules out vacuous constant-function witnesses.
This module imports neither the construction nor its proof.
-/

namespace QueryComplexity

/-- The substantive target, excluding the vacuous `0 =o 0` example.
Using `Fin` permits arities to vary with `n` without hiding instance data
inside existential quantifiers. `R` and `comp` themselves are generic. -/
def TotalCompositionCounterexample : Prop :=
  ∃ (a b : ℕ → ℕ)
    (F : (n : ℕ) → BoolFn (Fin (a n)))
    (G : (n : ℕ) → BoolFn (Fin (b n))),
    (∀ n, 0 < R (F n) ∧ 0 < R (G n)) ∧
    Asymptotics.IsLittleO Filter.atTop
      (fun n => (R (comp (F n) (G n)) : ℝ))
      (fun n => (R (F n) : ℝ) * (R (G n) : ℝ))

end QueryComplexity
