# No Perfect Randomized Composition - Lean formalization

Lean **4.28.0**, with mathlib **v4.28.0** pinned in `lake-manifest.json`.

The main result is `total_total_composition_counterexample` in [Solution.lean](Solution.lean).
It states that there are total Boolean function families with positive randomized
query complexity for both factors and

```text
R(comp F_n G_n) = o(R(F_n) * R(G_n)).
```

`R` uses finite probability distributions over deterministic decision trees,
worst-case query depth, and success at least 2/3 on every input. Block composition
uses a Cartesian product of coordinate types.

## Organization

The dependencies go in one direction:

```text
Mathlib -> ForMathlib -> QueryComplexity -> Main/ -> Solution.lean
```

- **[ForMathlib/](ForMathlib/)** contains general mathematics with no imports from
  query complexity: finite weighted probability, Bernoulli sums and posteriors,
  binomial estimates, finite counting, linear codes and private fibers, and
  `Function.blockComp` for general input/output types.
  The semantic namespaces are independent of `QueryComplexity`.
- **[QueryComplexity/Basic.lean](QueryComplexity/Basic.lean)** defines Boolean
  functions, decision trees, randomized query bounds, and `R`. It proves
  feasibility, attainment, zero-complexity and nonconstancy facts, invariance
  under coordinate changes, reductions, and the basic composition lower bounds.
- **[QueryComplexity/](QueryComplexity/)** contains reusable query arguments.
  `DecisionTree/`, `Randomized/`, `LowerBounds/`, `Encoding/`, and `Algorithms/`
  hold the general machinery. The public family entry points are
  [CheatSheet.lean](QueryComplexity/CheatSheet.lean),
  [ApproxIndex.lean](QueryComplexity/ApproxIndex.lean), and
  [PointerFunction.lean](QueryComplexity/PointerFunction.lean).
  ApproxIndex is retained because its promise, evaluation algorithms, and
  distributional lower bounds are used independently of the final parameter choice.
- **[Main/](Main/)** chooses the parameters and combines those reusable results.
  Construction-specific numerical constants live here rather than in `ForMathlib`.
- **[Solution.lean](Solution.lean)** proves the final theorem and checks its
  transitive axioms with `#guard_msgs`.

Import `ForMathlib`, `QueryComplexity`, or one public family module to use the
corresponding library. Import `Solution` to obtain the completed separation theorem.
Importing `QueryComplexity` does not import the counterexample or its statement.

## Proof map

| Module | Role |
| --- | --- |
| `Main/Statement.lean` | Exact existential little-o target; independent of its proof |
| `Main/Construction.lean` | Parameters, concrete outer and inner functions, sparse indexing, positivity |
| `Main/OuterLowerBound.lean` | Approximate-index hard distribution, list direct product, private-cell hybrid, and outer lower bound |
| `Main/InnerNumerics.lean` | Quantitative estimates for the chosen pointer-majority parameters |
| `Main/InnerLowerBound.lean` | Central-layer cell lower bound and transfer through the encoding |
| `Main/UpperBound.lean` | Algorithm for the composed function, including exact verification |
| `Main/Comparison.lean` | Compares costs and converts the vanishing ratio into the target statement |
| `Solution.lean` | Joins the independently proved bounds |

The functions retain their declaration names `QueryComplexity.Construction.F`
and `.G`; their definitions now live in `Main/Construction.lean`.

## Build and audit

From this directory:

```powershell
lake build
```

This builds the reusable libraries, the construction, and `Solution.lean`,
including the guarded axiom check. The main targets can also be built separately:

```powershell
lake build ForMathlib
lake build QueryComplexity
lake build Solution
```

The Lake configuration enables mathlib's standard linter set globally, including
the check for fragile nonterminal simplification.

To check the solution entry point directly:

```powershell
lake env lean Solution.lean
```

Its `#guard_msgs` check requires exactly `propext`, `Classical.choice`, and
`Quot.sound`; an added axiom makes compilation fail.

The cleanup was checked with `Batteries.Tactic.ShowUnused` and a transitive
dependency audit from the final theorem. `#show_unused` checks declarations in
the current file, so module audits use the public results consumed elsewhere
as their roots. General library results remain public even when this particular
counterexample does not use them; one-off arithmetic helpers are private.

[Comparator.lean](Comparator.lean) is the original minimal reference certificate.
It imports `Main.Statement`, which contains no construction or separation proof,
and retains its one intentionally requested `sorry`. No library or proof imports
that certificate. It is excluded from the default build and can be checked
separately with `lake env lean Comparator.lean`.
