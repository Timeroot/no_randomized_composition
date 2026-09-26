import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# The definitions used by the composition comparator

Randomized algorithms are finite probability distributions on deterministic
decision trees, with a worst-case depth bound and success at least `2/3`
on **every** input. For a finite coordinate type, this is the usual
bounded-error randomized query model: there are only finitely many trees
of any given bounded depth.

No computational or query-complexity theorem is assumed in this file.
-/

open scoped BigOperators

namespace QueryComplexity

universe u v

/-- A total Boolean function with coordinate type `T`. -/
abbrev BoolFn (T : Type u) := (T → Bool) → Bool

/-- Deterministic query trees; repeated queries are allowed and counted.
The output type is generic so that direct-product and list algorithms use
the same decision-tree model. Query complexity specializes it to `Bool`. -/
inductive DecisionTree (T : Type u) (Output : Type v) where
  | leaf (answer : Output)
  | node (coordinate : T) (zero one : DecisionTree T Output)

namespace DecisionTree

/-- On answer `false`, take the zero branch; on `true`, take the one branch. -/
def eval {T : Type u} {Output : Type v} :
    DecisionTree T Output → (T → Bool) → Output
  | .leaf answer, _ => answer
  | .node i zero one, x => if x i then eval one x else eval zero x

/-- The maximum number of coordinate queries on any execution. -/
def depth {T : Type u} {Output : Type v} : DecisionTree T Output → ℕ
  | .leaf _ => 0
  | .node _ zero one => 1 + max (depth zero) (depth one)

end DecisionTree

/-- A finite randomized decision tree computes `f` at depth at most `d`,
with worst-input error at most `1/3`. Weights are real probabilities;
the support may contain repeated deterministic trees. -/
def HasRandomizedBound {T : Type u} (f : BoolFn T) (d : ℕ) : Prop :=
  ∃ (m : ℕ) (tree : Fin m → DecisionTree T Bool) (weight : Fin m → ℝ),
    (∀ i, (tree i).depth ≤ d) ∧
    (∀ i, 0 ≤ weight i) ∧
    (∑ i, weight i) = 1 ∧
    ∀ x, (2 : ℝ) / 3 ≤
      ∑ i, if (tree i).eval x = f x then weight i else 0

/-- Standard bounded-error randomized query complexity. The feasible set
is nonempty for a finite coordinate type, as proved in `Basic.lean`. -/
noncomputable def R {T : Type u} [Fintype T] (f : BoolFn T) : ℕ :=
  sInf {d : ℕ | HasRandomizedBound f d}

/-- Standard block composition. The input is equivalently a function
`T₁ → T₂ → Bool`: one `T₂`-block for each `T₁` coordinate. -/
def comp {T₁ : Type u} {T₂ : Type v}
    (f : BoolFn T₁) (g : BoolFn T₂) : BoolFn (T₁ × T₂) :=
  fun x => f (fun i => g (fun j => x (i, j)))

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
