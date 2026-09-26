import QueryComplexity.FamilyComparison
import QueryComplexity.FamilyInnerLower

/-! The completed theorem has exactly the comparator's statement.
This module does not import `Comparator`, directly or indirectly. -/

theorem total_total_composition_counterexample :
    QueryComplexity.TotalCompositionCounterexample :=
  QueryComplexity.Construction.counterexample_of_eventual_inner_lower
    QueryComplexity.Construction.eventually_R_G_lower
