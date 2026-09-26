This project formalizes a separation from perfect randomized query composition
for total Boolean functions in Lean 4.28.0 with mathlib 4.28.0.

`Comparator.lean` is the minimal reference certificate. It imports only the
definitions and contains the requested single `sorry`. `QueryComplexity/Proof.lean`
proves the same statement independently; the proof library never imports the
comparator.

The model uses finite probability distributions on deterministic query trees,
worst-case depth, and success probability at least 2/3 on every input. Standard
block composition has coordinates `T₁ × T₂`, or curried input
`T₁ → T₂ → Bool`. The statement requires both factors to have positive query
complexity, excluding the vacuous constant-function example.

The concrete families are `Construction.F` and `Construction.G` in
`QueryComplexity/Families.lean`. Their outer lower bound, inner lower bound, and
composed upper bound are joined in `QueryComplexity/Proof.lean`.

Build and audit:

```powershell
lake build
lake env lean Proof.lean
```

The second command prints the final theorem's transitive axiom dependencies.
The full build passes. The final theorem depends only on `propext`,
`Classical.choice`, and `Quot.sound`; its proof has no admissions or added axioms.
The separate reference certificate can be checked with
`lake env lean Comparator.lean`; its placeholder intentionally produces a
`sorry` warning.
