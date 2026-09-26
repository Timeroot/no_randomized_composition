import QueryComplexity.Basic

/-!
# Deterministic decision-tree operations

Sequential execution, finite coordinate reads, and compilation of bounded
oracle programs all carry evaluation and worst-case depth specifications.
-/

open scoped BigOperators

namespace QueryComplexity
namespace DecisionTree

universe u v w

variable {T : Type u} {A : Type v} {B : Type w}

/-- Replace each leaf by the continuation selected by that leaf's answer. -/
def bind (tree : DecisionTree T A) (next : A → DecisionTree T B) : DecisionTree T B :=
  match tree with
  | .leaf answer => next answer
  | .node i zero one => .node i (zero.bind next) (one.bind next)

@[simp] theorem eval_bind (tree : DecisionTree T A) (next : A → DecisionTree T B)
    (x : T → Bool) : (tree.bind next).eval x = (next (tree.eval x)).eval x := by
  induction tree with
  | leaf answer => rfl
  | node i zero one hz ho => cases hx : x i <;> simp [bind, eval, hx, hz, ho]

/-- Sequential computation adds the uniform worst-case depth of its continuation. -/
theorem depth_bind_le (tree : DecisionTree T A) (next : A → DecisionTree T B)
    {e : ℕ} (hnext : ∀ a, (next a).depth ≤ e) :
    (tree.bind next).depth ≤ tree.depth + e := by
  induction tree with
  | leaf answer => simpa [bind, depth] using hnext answer
  | node i zero one hz ho => grind [bind, depth]

theorem depth_bind_le_add (tree : DecisionTree T A) (next : A → DecisionTree T B)
    {d e : ℕ} (htree : tree.depth ≤ d) (hnext : ∀ a, (next a).depth ≤ e) :
    (tree.bind next).depth ≤ d + e :=
  (depth_bind_le tree next hnext).trans (Nat.add_le_add_right htree e)

/-- A single exact input query. -/
def query (i : T) : DecisionTree T Bool := .node i (.leaf false) (.leaf true)

@[simp] theorem eval_query (i : T) (x : T → Bool) : (query i).eval x = x i := by
  cases hx : x i <;> simp [query, eval, hx]

@[simp] theorem depth_query (i : T) : (query i).depth = 1 := rfl

/-- Query any finite indexed collection of coordinates, returning its answers.
The coordinate map need not be injective. -/
noncomputable def readCoordinates {S : Type v} [Fintype S] (coordinate : S → T) :
    DecisionTree T (S → Bool) :=
  (Classical.choose (exists_read_all (T := S) (fun x => x))).substitute
    (fun i => .inr (coordinate i, id))

@[simp] theorem eval_readCoordinates {S : Type v} [Fintype S]
    (coordinate : S → T) (x : T → Bool) :
    (readCoordinates coordinate).eval x = fun i => x (coordinate i) := by
  simp only [readCoordinates, eval_substitute]
  exact (Classical.choose_spec (exists_read_all (T := S) (fun x => x))).1 _

theorem depth_readCoordinates_le {S : Type v} [Fintype S] (coordinate : S → T) :
    (readCoordinates coordinate).depth ≤ Fintype.card S :=
  (depth_substitute_le _ _).trans
    (Classical.choose_spec (exists_read_all (T := S) (fun x => x))).2

/-- Run two trees sequentially and return both outputs. -/
def pair (first : DecisionTree T A) (second : DecisionTree T B) : DecisionTree T (A × B) :=
  first.bind (fun a => second.mapOutput (fun b => (a, b)))

@[simp] theorem eval_pair (first : DecisionTree T A) (second : DecisionTree T B)
    (x : T → Bool) : (first.pair second).eval x = (first.eval x, second.eval x) := by
  simp [pair]

theorem depth_pair_le (first : DecisionTree T A) (second : DecisionTree T B) :
    (first.pair second).depth ≤ first.depth + second.depth := by
  exact depth_bind_le first _ (by simp)

end DecisionTree

universe u v w

/-- One step of a deterministic oracle program. -/
inductive QueryStep (Query : Type u) (Answer : Type v) (State : Type w) (Output : Type*) where
  | done (answer : Output)
  | ask (query : Query) (next : Answer → State)

namespace QueryStep

variable {Query : Type u} {Answer : Type v} {State : Type w} {Output : Type*}

/-- Execute a program for at most `fuel` steps, using a fixed fallback on timeout. -/
def run (step : State → QueryStep Query Answer State Output) (fallback : Output)
    (oracle : Query → Answer) : ℕ → State → Output
  | 0, _ => fallback
  | fuel + 1, state =>
      match step state with
      | .done answer => answer
      | .ask query next => run step fallback oracle fuel (next (oracle query))

/-- Compile a bounded oracle program into the original binary decision-tree model. -/
def compile {T : Type*} (step : State → QueryStep Query Answer State Output)
    (fallback : Output) (queryTree : Query → DecisionTree T Answer) :
    ℕ → State → DecisionTree T Output
  | 0, _ => .leaf fallback
  | fuel + 1, state =>
      match step state with
      | .done answer => .leaf answer
      | .ask query next => (queryTree query).bind
          (fun answer => compile step fallback queryTree fuel (next answer))

theorem eval_compile {T : Type*} (step : State → QueryStep Query Answer State Output)
    (fallback : Output) (queryTree : Query → DecisionTree T Answer)
    (oracle : (T → Bool) → Query → Answer)
    (hquery : ∀ q x, (queryTree q).eval x = oracle x q)
    (fuel : ℕ) (state : State) (x : T → Bool) :
    (compile step fallback queryTree fuel state).eval x = run step fallback (oracle x) fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases hs : step state with
      | done answer => simp [compile, run, hs, DecisionTree.eval]
      | ask query next => simp [compile, run, hs, hquery, ih]

theorem depth_compile_le {T : Type*} (step : State → QueryStep Query Answer State Output)
    (fallback : Output) (queryTree : Query → DecisionTree T Answer) {cost : ℕ}
    (hquery : ∀ q, (queryTree q).depth ≤ cost) (fuel : ℕ) (state : State) :
    (compile step fallback queryTree fuel state).depth ≤ fuel * cost := by
  induction fuel generalizing state with
  | zero => simp [compile, DecisionTree.depth]
  | succ fuel ih =>
      cases hs : step state with
      | done answer => simp [compile, hs, DecisionTree.depth]
      | ask query next =>
          have h := DecisionTree.depth_bind_le_add (queryTree query)
            (fun answer => compile step fallback queryTree fuel (next answer)) (hquery query)
            (fun answer => ih (next answer))
          simpa [compile, hs, Nat.succ_mul, Nat.add_comm] using h

/-- A decreasing natural potential certifies that the cap cannot cause a
timeout while an invariant holds. -/
theorem run_spec_of_decreasing (step : State → QueryStep Query Answer State Output)
    (fallback : Output) (oracle : Query → Answer)
    (invariant : State → Prop) (postcondition : Output → Prop) (potential : State → ℕ)
    (hstep : ∀ state, invariant state →
      match step state with
      | .done answer => postcondition answer
      | .ask query next => invariant (next (oracle query)) ∧
          potential (next (oracle query)) < potential state)
    (fuel : ℕ) (state : State) (hstate : invariant state) (hfuel : potential state < fuel) :
    postcondition (run step fallback oracle fuel state) := by
  induction fuel generalizing state with
  | zero => omega
  | succ fuel ih =>
      have h := hstep state hstate
      cases hs : step state with
      | done answer => simpa [run, hs] using h
      | ask query next => grind [run]
end QueryStep

end QueryComplexity
