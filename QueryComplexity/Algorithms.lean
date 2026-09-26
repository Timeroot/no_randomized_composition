import QueryComplexity.Reindex

/-! Cost-certified deterministic and finite randomized algorithm combinators. -/

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
  | node i zero one hz ho => simp only [bind, depth]; omega

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
  apply depth_bind_le
  intro a
  simp

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
      | ask query next =>
          simp only [hs] at h
          simpa only [run, hs] using ih (next (oracle query)) h.1 (by omega)
end QueryStep

/-- A finite distribution on deterministic trees, with an arbitrary finite
seed type. Its normalization is part of the data. -/
structure FiniteRandomizedTree (Seed : Type u) [Fintype Seed] (T : Type v) (Output : Type w) where
  tree : Seed → DecisionTree T Output
  weight : Seed → ℝ
  weight_nonneg : ∀ s, 0 ≤ weight s
  weight_sum : (∑ s, weight s) = 1

namespace FiniteRandomizedTree

variable {Seed : Type u} [Fintype Seed] {T : Type v} {Output : Type w}

/-- Choose a seed uniformly from a nonempty finite type. -/
noncomputable def uniform [Nonempty Seed] (tree : Seed → DecisionTree T Output) :
    FiniteRandomizedTree Seed T Output where
  tree := tree
  weight _ := (Fintype.card Seed : ℝ)⁻¹
  weight_nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  weight_sum := by
    have hcard : (Fintype.card Seed : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [hcard]

def DepthBound (algorithm : FiniteRandomizedTree Seed T Output) (d : ℕ) : Prop :=
  ∀ s, (algorithm.tree s).depth ≤ d

noncomputable def probability (algorithm : FiniteRandomizedTree Seed T Output)
    (event : Output → Prop) (x : T → Bool) : ℝ := by
  classical
  exact ∑ s, if event ((algorithm.tree s).eval x) then algorithm.weight s else 0

theorem probability_nonneg (algorithm : FiniteRandomizedTree Seed T Output)
    (event : Output → Prop) (x : T → Bool) : 0 ≤ algorithm.probability event x := by
  classical
  apply Finset.sum_nonneg
  intro s _
  split_ifs
  · exact algorithm.weight_nonneg s
  · exact le_rfl

theorem probability_le_one (algorithm : FiniteRandomizedTree Seed T Output)
    (event : Output → Prop) (x : T → Bool) : algorithm.probability event x ≤ 1 := by
  classical
  rw [← algorithm.weight_sum]
  apply Finset.sum_le_sum
  intro s _
  split_ifs
  · exact le_rfl
  · exact algorithm.weight_nonneg s

theorem probability_mono (algorithm : FiniteRandomizedTree Seed T Output)
    {p q : Output → Prop} (hpq : ∀ a, p a → q a) (x : T → Bool) :
    algorithm.probability p x ≤ algorithm.probability q x := by
  classical
  apply Finset.sum_le_sum
  intro s _
  split_ifs with hp hq hq
  · rfl
  · exact (hq (hpq _ hp)).elim
  · exact algorithm.weight_nonneg s
  · rfl

@[simp] theorem probability_true (algorithm : FiniteRandomizedTree Seed T Output)
    (x : T → Bool) : algorithm.probability (fun _ => True) x = 1 := by
  unfold probability
  simpa using algorithm.weight_sum

theorem probability_or_of_disjoint (algorithm : FiniteRandomizedTree Seed T Output)
    (p q : Output → Prop) (hdisjoint : ∀ a, ¬ (p a ∧ q a)) (x : T → Bool) :
    algorithm.probability (fun a => p a ∨ q a) x =
      algorithm.probability p x + algorithm.probability q x := by
  classical
  unfold probability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> simp_all

theorem probability_not (algorithm : FiniteRandomizedTree Seed T Output)
    (p : Output → Prop) (x : T → Bool) :
    algorithm.probability (fun a => ¬ p a) x = 1 - algorithm.probability p x := by
  classical
  have h := algorithm.probability_or_of_disjoint p (fun a => ¬ p a) (by simp) x
  have hall : (fun a => p a ∨ ¬ p a) = fun _ => True := by
    funext a
    apply propext
    tauto
  rw [hall, probability_true] at h
  linarith

/-- Apply a deterministic function to the output without making queries. -/
def mapOutput {Output' : Type*} (algorithm : FiniteRandomizedTree Seed T Output)
    (decode : Output → Output') : FiniteRandomizedTree Seed T Output' where
  tree s := (algorithm.tree s).mapOutput decode
  weight := algorithm.weight
  weight_nonneg := algorithm.weight_nonneg
  weight_sum := algorithm.weight_sum

@[simp] theorem depthBound_mapOutput {Output' : Type*}
    (algorithm : FiniteRandomizedTree Seed T Output) (decode : Output → Output') (d : ℕ) :
    (algorithm.mapOutput decode).DepthBound d ↔ algorithm.DepthBound d := by
  simp [DepthBound, mapOutput]

@[simp] theorem probability_mapOutput {Output' : Type*}
    (algorithm : FiniteRandomizedTree Seed T Output) (decode : Output → Output')
    (event : Output' → Prop) (x : T → Bool) :
    (algorithm.mapOutput decode).probability event x =
      algorithm.probability (fun a => event (decode a)) x := by
  classical
  unfold probability mapOutput
  apply Finset.sum_congr rfl
  intro s _
  rw [DecisionTree.eval_mapOutput]

/-- Lift an algorithm through a single-bit input substitution. -/
def substitute {U : Type*} (algorithm : FiniteRandomizedTree Seed T Output)
    (σ : BitSubstitution U T) : FiniteRandomizedTree Seed U Output where
  tree s := (algorithm.tree s).substitute σ
  weight := algorithm.weight
  weight_nonneg := algorithm.weight_nonneg
  weight_sum := algorithm.weight_sum

theorem depthBound_substitute {U : Type*} (algorithm : FiniteRandomizedTree Seed T Output)
    (σ : BitSubstitution U T) {d : ℕ} (h : algorithm.DepthBound d) :
    (algorithm.substitute σ).DepthBound d := by
  intro s
  exact ((algorithm.tree s).depth_substitute_le σ).trans (h s)

@[simp] theorem probability_substitute {U : Type*}
    (algorithm : FiniteRandomizedTree Seed T Output) (σ : BitSubstitution U T)
    (event : Output → Prop) (x : U → Bool) :
    (algorithm.substitute σ).probability event x = algorithm.probability event (σ.eval x) := by
  classical
  unfold probability substitute
  apply Finset.sum_congr rfl
  intro s _
  rw [DecisionTree.eval_substitute]

/-- Uniformly choose a member of a finite family of randomized algorithms. -/
noncomputable def uniformChoice {Choice : Type*} [Fintype Choice] [Nonempty Choice]
    (family : Choice → FiniteRandomizedTree Seed T Output) :
    FiniteRandomizedTree (Choice × Seed) T Output where
  tree s := (family s.1).tree s.2
  weight s := (Fintype.card Choice : ℝ)⁻¹ * (family s.1).weight s.2
  weight_nonneg s := mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    ((family s.1).weight_nonneg _)
  weight_sum := by
    have hcard : (Fintype.card Choice : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, weight_sum]
    simp [hcard]

theorem depthBound_uniformChoice {Choice : Type*} [Fintype Choice] [Nonempty Choice]
    (family : Choice → FiniteRandomizedTree Seed T Output) {d : ℕ}
    (h : ∀ s, (family s).DepthBound d) : (uniformChoice family).DepthBound d :=
  fun s => h s.1 s.2

theorem probability_uniformChoice {Choice : Type*} [Fintype Choice] [Nonempty Choice]
    (family : Choice → FiniteRandomizedTree Seed T Output)
    (event : Output → Prop) (x : T → Bool) :
    (uniformChoice family).probability event x =
      (Fintype.card Choice : ℝ)⁻¹ * ∑ s, (family s).probability event x := by
  classical
  unfold probability uniformChoice
  simp only [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> simp

/-- A biased coin is a zero-query finite randomized tree. -/
def coin (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : FiniteRandomizedTree Bool T Bool where
  tree b := .leaf b
  weight b := if b then p else 1 - p
  weight_nonneg b := by cases b <;> simp [hp₀, sub_nonneg.mpr hp₁]
  weight_sum := by simp

theorem depthBound_coin (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    (coin (T := T) p hp₀ hp₁).DepthBound 0 := fun _ => le_rfl

@[simp] theorem probability_coin_true (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (x : T → Bool) :
    (coin p hp₀ hp₁).probability (fun b => b = true) x = p := by
  simp [probability, coin, DecisionTree.eval]

theorem probability_false (algorithm : FiniteRandomizedTree Seed T Bool) (x : T → Bool) :
    algorithm.probability (fun b => b = false) x = 1 - algorithm.probability (fun b => b = true) x := by
  have heq : (fun b : Bool => b = false) = fun b => ¬ b = true := by
    funext b
    cases b <;> simp
  rw [heq, probability_not]

/-- Independent sequential execution uses the product distribution of seeds. -/
def pair {Seed' : Type*} [Fintype Seed'] {Output' : Type*}
    (first : FiniteRandomizedTree Seed T Output)
    (second : FiniteRandomizedTree Seed' T Output') :
    FiniteRandomizedTree (Seed × Seed') T (Output × Output') where
  tree s := (first.tree s.1).pair (second.tree s.2)
  weight s := first.weight s.1 * second.weight s.2
  weight_nonneg s := mul_nonneg (first.weight_nonneg _) (second.weight_nonneg _)
  weight_sum := by
    simp [Fintype.sum_prod_type, ← Finset.mul_sum, first.weight_sum, second.weight_sum]

theorem depthBound_pair {Seed' : Type*} [Fintype Seed'] {Output' : Type*}
    (first : FiniteRandomizedTree Seed T Output)
    (second : FiniteRandomizedTree Seed' T Output') {d e : ℕ}
    (hfirst : first.DepthBound d) (hsecond : second.DepthBound e) :
    (first.pair second).DepthBound (d + e) := by
  intro s
  exact ((first.tree s.1).depth_pair_le (second.tree s.2)).trans
    (Nat.add_le_add (hfirst _) (hsecond _))

theorem probability_pair {Seed' : Type*} [Fintype Seed'] {Output' : Type*}
    (first : FiniteRandomizedTree Seed T Output)
    (second : FiniteRandomizedTree Seed' T Output')
    (p : Output → Prop) (q : Output' → Prop) (x : T → Bool) :
    (first.pair second).probability (fun a => p a.1 ∧ q a.2) x =
      first.probability p x * second.probability q x := by
  classical
  simp only [probability, pair, DecisionTree.eval_pair, Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> simp_all

/-- Independently run two Boolean algorithms and OR their outputs. -/
def or {Seed' : Type*} [Fintype Seed']
    (first : FiniteRandomizedTree Seed T Bool) (second : FiniteRandomizedTree Seed' T Bool) :
    FiniteRandomizedTree (Seed × Seed') T Bool :=
  (first.pair second).mapOutput (fun b => b.1 || b.2)

theorem depthBound_or {Seed' : Type*} [Fintype Seed']
    (first : FiniteRandomizedTree Seed T Bool) (second : FiniteRandomizedTree Seed' T Bool)
    {d e : ℕ} (hfirst : first.DepthBound d) (hsecond : second.DepthBound e) :
    (first.or second).DepthBound (d + e) := by
  simpa [or] using first.depthBound_pair second hfirst hsecond

theorem probability_or_true {Seed' : Type*} [Fintype Seed']
    (first : FiniteRandomizedTree Seed T Bool) (second : FiniteRandomizedTree Seed' T Bool)
    (x : T → Bool) :
    (first.or second).probability (fun b => b = true) x =
      first.probability (fun b => b = true) x +
        (1 - first.probability (fun b => b = true) x) * second.probability (fun b => b = true) x := by
  have heq : (fun b : Bool × Bool => (b.1 || b.2) = false) =
      fun b => b.1 = false ∧ b.2 = false := by
    funext b
    rcases b with ⟨a, b⟩
    cases a <;> cases b <;> simp
  have hfalse : (first.or second).probability (fun b => b = false) x =
      (1 - first.probability (fun b => b = true) x) *
        (1 - second.probability (fun b => b = true) x) := by
    unfold or
    rw [probability_mapOutput, heq,
      first.probability_pair second (fun b => b = false) (fun b => b = false) x,
      probability_false, probability_false]
  rw [probability_false] at hfalse
  nlinarith

/-- Arbitrary finite seed types give the same standard randomized model as
the `Fin m` distributions in `HasRandomizedBound`. -/
theorem toHasRandomizedBound (algorithm : FiniteRandomizedTree Seed T Bool)
    {f : BoolFn T} {d : ℕ} (hdepth : algorithm.DepthBound d)
    (hsuccess : ∀ x, (2 : ℝ) / 3 ≤ algorithm.probability (fun b => b = f x) x) :
    HasRandomizedBound f d := by
  classical
  let e := Fintype.equivFin Seed
  refine ⟨Fintype.card Seed, fun i => algorithm.tree (e.symm i),
    fun i => algorithm.weight (e.symm i), fun i => hdepth _,
    fun i => algorithm.weight_nonneg _, ?_, ?_⟩
  · exact (e.symm.sum_comp algorithm.weight).trans algorithm.weight_sum
  · intro x
    apply (hsuccess x).trans_eq
    unfold probability
    trans ∑ s, if (algorithm.tree s).eval x = f x then algorithm.weight s else 0
    · apply Finset.sum_congr rfl
      intro s _
      split_ifs <;> rfl
    · exact (e.symm.sum_comp
        (fun s => if (algorithm.tree s).eval x = f x then algorithm.weight s else 0)).symm

/-- Majority vote among three independent executions. -/
def majority3 (algorithm : FiniteRandomizedTree Seed T Bool) :
    FiniteRandomizedTree (Seed × (Seed × Seed)) T Bool :=
  (algorithm.pair (algorithm.pair algorithm)).mapOutput
    (fun b => (b.1 && b.2.1) || (b.1 && b.2.2) || (b.2.1 && b.2.2))

theorem depthBound_majority3 (algorithm : FiniteRandomizedTree Seed T Bool)
    {d : ℕ} (h : algorithm.DepthBound d) : algorithm.majority3.DepthBound (3 * d) := by
  have hp := algorithm.depthBound_pair (algorithm.pair algorithm) h
    (algorithm.depthBound_pair algorithm h h)
  simpa [majority3, show d + (d + d) = 3 * d by omega] using hp

/-- The exact majority-of-three error polynomial. -/
theorem probability_majority3_error (algorithm : FiniteRandomizedTree Seed T Bool)
    (answer : Bool) (x : T → Bool) :
    algorithm.majority3.probability (fun b => b ≠ answer) x =
      3 * (algorithm.probability (fun b => b ≠ answer) x) ^ 2 -
        2 * (algorithm.probability (fun b => b ≠ answer) x) ^ 3 := by
  classical
  let p : Bool → Prop := fun b => b ≠ answer
  let triple := algorithm.pair (algorithm.pair algorithm)
  let e₀ : Bool × (Bool × Bool) → Prop := fun b => p b.1 ∧ (p b.2.1 ∧ True)
  let e₁ : Bool × (Bool × Bool) → Prop := fun b => p b.1 ∧ (¬ p b.2.1 ∧ p b.2.2)
  let e₂ : Bool × (Bool × Bool) → Prop := fun b => ¬ p b.1 ∧ (p b.2.1 ∧ p b.2.2)
  have hsplit : (fun b : Bool × (Bool × Bool) =>
      ((b.1 && b.2.1) || (b.1 && b.2.2) || (b.2.1 && b.2.2)) ≠ answer) =
      (fun b => e₀ b ∨ (e₁ b ∨ e₂ b)) := by
    funext b
    rcases b with ⟨a, b, c⟩
    cases a <;> cases b <;> cases c <;> cases answer <;> decide
  have hd₀ : ∀ b, ¬ (e₀ b ∧ (e₁ b ∨ e₂ b)) := by simp [e₀, e₁, e₂]; tauto
  have hd₁ : ∀ b, ¬ (e₁ b ∧ e₂ b) := by simp [e₁, e₂]; tauto
  have h₀ : triple.probability e₀ x =
      algorithm.probability p x * algorithm.probability p x := by
    rw [show triple.probability e₀ x = algorithm.probability p x *
      (algorithm.pair algorithm).probability (fun b => p b.1 ∧ True) x from
        algorithm.probability_pair (algorithm.pair algorithm) p (fun b => p b.1 ∧ True) x]
    rw [algorithm.probability_pair algorithm p (fun _ => True) x, probability_true, mul_one]
  have h₁ : triple.probability e₁ x =
      algorithm.probability p x * ((1 - algorithm.probability p x) *
        algorithm.probability p x) := by
    rw [show triple.probability e₁ x = algorithm.probability p x *
      (algorithm.pair algorithm).probability (fun b => ¬ p b.1 ∧ p b.2) x from
        algorithm.probability_pair (algorithm.pair algorithm) p (fun b => ¬ p b.1 ∧ p b.2) x]
    rw [algorithm.probability_pair algorithm (fun b => ¬ p b) p x,
      algorithm.probability_not p x]
  have h₂ : triple.probability e₂ x =
      (1 - algorithm.probability p x) * (algorithm.probability p x *
        algorithm.probability p x) := by
    rw [show triple.probability e₂ x = algorithm.probability (fun b => ¬ p b) x *
      (algorithm.pair algorithm).probability (fun b => p b.1 ∧ p b.2) x from
        algorithm.probability_pair (algorithm.pair algorithm) (fun b => ¬ p b)
          (fun b => p b.1 ∧ p b.2) x]
    rw [algorithm.probability_pair algorithm p p x, algorithm.probability_not p x]
  change (triple.mapOutput _).probability _ x = _
  rw [probability_mapOutput, hsplit,
    probability_or_of_disjoint triple e₀ (fun b => e₁ b ∨ e₂ b) hd₀,
    probability_or_of_disjoint triple e₁ e₂ hd₁]
  rw [h₀, h₁, h₂]
  dsimp [p]
  ring

/-- A convenient quadratic upper bound for amplification. -/
theorem probability_majority3_error_le (algorithm : FiniteRandomizedTree Seed T Bool)
    (answer : Bool) (x : T → Bool) {ε : ℝ}
    (hε : 0 ≤ ε) (herror : algorithm.probability (fun b => b ≠ answer) x ≤ ε) :
    algorithm.majority3.probability (fun b => b ≠ answer) x ≤ 3 * ε ^ 2 := by
  have hp := algorithm.probability_nonneg (fun b => b ≠ answer) x
  have hp3 : 0 ≤ algorithm.probability (fun b => b ≠ answer) x ^ 3 := pow_nonneg hp _
  rw [probability_majority3_error]
  nlinarith [sq_le_sq₀ hp hε |>.2 herror]

theorem probability_majority3_error_le_polynomial
    (algorithm : FiniteRandomizedTree Seed T Bool) (answer : Bool) (x : T → Bool) {ε : ℝ}
    (hε : 0 ≤ ε) (hhalf : ε ≤ 1 / 2)
    (herror : algorithm.probability (fun b => b ≠ answer) x ≤ ε) :
    algorithm.majority3.probability (fun b => b ≠ answer) x ≤ 3 * ε ^ 2 - 2 * ε ^ 3 := by
  let p := algorithm.probability (fun b => b ≠ answer) x
  have hp : 0 ≤ p := algorithm.probability_nonneg _ _
  have hpe : p ≤ ε := herror
  have hpHalf : p ≤ 1 / 2 := hpe.trans hhalf
  have hεsq := mul_nonneg hε (sub_nonneg.mpr hhalf)
  have hpsq := mul_nonneg hp (sub_nonneg.mpr hpHalf)
  have hεp := mul_nonneg hε (sub_nonneg.mpr hpHalf)
  have hbracket : 0 ≤ 3 * (ε + p) - 2 * (ε ^ 2 + ε * p + p ^ 2) := by
    nlinarith
  have hfactor := mul_nonneg (sub_nonneg.mpr hpe) hbracket
  rw [probability_majority3_error]
  change 3 * p ^ 2 - 2 * p ^ 3 ≤ _
  nlinarith

/-- Three constant-size majority stages reduce error `1/3` to at most `1/6`. -/
theorem probability_majority3_three_error (algorithm : FiniteRandomizedTree Seed T Bool)
    (answer : Bool) (x : T → Bool)
    (herror : algorithm.probability (fun b => b ≠ answer) x ≤ 1 / 3) :
    algorithm.majority3.majority3.majority3.probability (fun b => b ≠ answer) x ≤ 1 / 6 := by
  have h₁ : algorithm.majority3.probability (fun b => b ≠ answer) x ≤ 7 / 27 := by
    have h := algorithm.probability_majority3_error_le_polynomial answer x
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num) herror
    norm_num at h ⊢
    exact h
  have h₂ : algorithm.majority3.majority3.probability (fun b => b ≠ answer) x ≤ 1 / 5 := by
    have h := algorithm.majority3.probability_majority3_error_le_polynomial answer x
      (by norm_num : (0 : ℝ) ≤ 7 / 27) (by norm_num) h₁
    linarith
  have h₃ := algorithm.majority3.majority3.probability_majority3_error_le_polynomial answer x
    (by norm_num : (0 : ℝ) ≤ 1 / 5) (by norm_num) h₂
  linarith

/-- Seeds for iterated independent majority stages. -/
def MajoritySeed (Seed : Type u) : ℕ → Type u
  | 0 => Seed
  | n + 1 => MajoritySeed Seed n × (MajoritySeed Seed n × MajoritySeed Seed n)

instance instFintypeMajoritySeed (Seed : Type u) [Fintype Seed] (n : ℕ) :
    Fintype (MajoritySeed Seed n) :=
  match n with
  | 0 => inferInstanceAs (Fintype Seed)
  | n + 1 => by
      letI : Fintype (MajoritySeed Seed n) := instFintypeMajoritySeed Seed n
      exact inferInstanceAs (Fintype (MajoritySeed Seed n ×
        (MajoritySeed Seed n × MajoritySeed Seed n)))

/-- An actual finite distribution on trees for every number of majority stages. -/
def iterateMajority3 (algorithm : FiniteRandomizedTree Seed T Bool) (n : ℕ) :
    FiniteRandomizedTree (MajoritySeed Seed n) T Bool :=
  match n with
  | 0 => algorithm
  | n + 1 => (iterateMajority3 algorithm n).majority3

theorem depthBound_iterateMajority3 (algorithm : FiniteRandomizedTree Seed T Bool)
    {d : ℕ} (hdepth : algorithm.DepthBound d) (n : ℕ) :
    (algorithm.iterateMajority3 n).DepthBound (3 ^ n * d) := by
  induction n with
  | zero => simpa [iterateMajority3] using hdepth
  | succ n ih =>
      have h := (algorithm.iterateMajority3 n).depthBound_majority3 ih
      simpa [iterateMajority3, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- Quadratic error decay at each stage gives a double-exponential error bound,
while the depth grows by `3^n`. -/
theorem probability_iterateMajority3_error
    (algorithm : FiniteRandomizedTree Seed T Bool) (answer : Bool) (x : T → Bool)
    (herror : algorithm.probability (fun b => b ≠ answer) x ≤ 1 / 6) (n : ℕ) :
    (algorithm.iterateMajority3 n).probability (fun b => b ≠ answer) x ≤
      (1 / 3 : ℝ) * (1 / 2 : ℝ) ^ (2 ^ n) := by
  induction n with
  | zero =>
      simpa only [iterateMajority3, pow_zero, pow_one,
        show (1 / 3 : ℝ) * (1 / 2) = 1 / 6 by norm_num] using herror
  | succ n ih =>
      change (algorithm.iterateMajority3 n).majority3.probability _ x ≤ _
      calc
        _ ≤ 3 * ((1 / 3 : ℝ) * (1 / 2 : ℝ) ^ (2 ^ n)) ^ 2 :=
          (algorithm.iterateMajority3 n).probability_majority3_error_le answer x (by positivity) ih
        _ = (1 / 3 : ℝ) * (1 / 2 : ℝ) ^ (2 ^ (n + 1)) := by
          rw [pow_succ (2 : ℕ) n, pow_mul]
          ring

/-- Amplification starting from the standard `1/3` error guarantee. -/
def amplify (algorithm : FiniteRandomizedTree Seed T Bool) (n : ℕ) :
    FiniteRandomizedTree (MajoritySeed (MajoritySeed Seed 3) n) T Bool :=
  (algorithm.iterateMajority3 3).iterateMajority3 n

theorem depthBound_amplify (algorithm : FiniteRandomizedTree Seed T Bool)
    {d : ℕ} (hdepth : algorithm.DepthBound d) (n : ℕ) :
    (algorithm.amplify n).DepthBound (27 * 3 ^ n * d) := by
  have h := (algorithm.iterateMajority3 3).depthBound_iterateMajority3
    (algorithm.depthBound_iterateMajority3 hdepth 3) n
  simpa [amplify, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem probability_amplify_error (algorithm : FiniteRandomizedTree Seed T Bool)
    (answer : Bool) (x : T → Bool)
    (herror : algorithm.probability (fun b => b ≠ answer) x ≤ 1 / 3) (n : ℕ) :
    (algorithm.amplify n).probability (fun b => b ≠ answer) x ≤
      (1 / 3 : ℝ) * (1 / 2 : ℝ) ^ (2 ^ n) := by
  apply probability_iterateMajority3_error
  exact algorithm.probability_majority3_three_error answer x herror

end FiniteRandomizedTree

/-- Every witness in the standard randomized-query model can be packaged as
a finite randomized tree with error at most `1/3` on every input. -/
theorem HasRandomizedBound.exists_algorithm {T : Type u} {f : BoolFn T} {d : ℕ}
    (h : HasRandomizedBound f d) :
    ∃ m, ∃ algorithm : FiniteRandomizedTree (Fin m) T Bool,
      algorithm.DepthBound d ∧
        ∀ x, algorithm.probability (fun b => b ≠ f x) x ≤ 1 / 3 := by
  classical
  rcases h with ⟨m, tree, weight, hdepth, hnonneg, hmass, hsuccess⟩
  let algorithm : FiniteRandomizedTree (Fin m) T Bool := ⟨tree, weight, hnonneg, hmass⟩
  refine ⟨m, algorithm, hdepth, ?_⟩
  intro x
  have hprob : algorithm.probability (fun b => b = f x) x =
      ∑ s, if (tree s).eval x = f x then weight s else 0 := by
    unfold FiniteRandomizedTree.probability algorithm
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> rfl
  have hn := algorithm.probability_not (fun b => b = f x) x
  rw [hprob] at hn
  change algorithm.probability (fun b => ¬ b = f x) x ≤ 1 / 3
  rw [hn]
  linarith [hsuccess x]

end QueryComplexity
