import Main.Statement

/-!
Minimal reference certificate. Its single `sorry` is the requested target,
not an imported assumption available to the eventual proof file.

The coordinates of block composition are `T₁ × T₂`, equivalently its input
has the curried type `T₁ → T₂ → Bool`. The type `T₁ → T₂` would instead
index bits by whole functions and describe a different query problem.

Positivity excludes constant-function witnesses: without it, `0 =o 0`
would satisfy the bare little-o statement trivially.
-/

theorem total_total_composition_counterexample :
    QueryComplexity.TotalCompositionCounterexample := by
  sorry
