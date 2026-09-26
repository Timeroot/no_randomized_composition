import Main.Comparison
import Main.InnerLowerBound

/-!
# No perfect randomized composition for total Boolean functions

The completed theorem has exactly the statement in `Main.Statement`.
The two factors have positive randomized query complexity. The proof joins
the independent outer lower bound, inner lower bound, and composed upper bound.
This module does not import `Comparator`, directly or indirectly.
-/

theorem total_total_composition_counterexample :
    QueryComplexity.TotalCompositionCounterexample :=
  QueryComplexity.Construction.counterexample_of_eventual_inner_lower
    QueryComplexity.Construction.eventually_R_G_lower

/-- info: 'total_total_composition_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms total_total_composition_counterexample
