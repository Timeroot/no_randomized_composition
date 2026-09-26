import ForMathlib.Function.BlockComposition
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic

/-!
# Randomized query complexity: the public basic interface

Total Boolean functions may use any finite coordinate type. Randomized
algorithms are finite probability distributions on deterministic trees,
with a worst-case depth bound and success at least `2/3` on every input.
This file defines that model and proves feasibility, attainment, the
zero-complexity characterization, invariance under coordinate changes,
and the elementary lower bounds for block composition.

No particular function family or separation theorem is imported.
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
is nonempty for a finite coordinate type, as proved below. -/
noncomputable def R {T : Type u} [Fintype T] (f : BoolFn T) : ℕ :=
  sInf {d : ℕ | HasRandomizedBound f d}

/-- Standard block composition. The input is equivalently a function
`T₁ → T₂ → Bool`: one `T₂`-block for each `T₁` coordinate. -/
def comp {T₁ : Type u} {T₂ : Type v}
    (f : BoolFn T₁) (g : BoolFn T₂) : BoolFn (T₁ × T₂) :=
  Function.blockComp f g

end QueryComplexity

namespace QueryComplexity

universe u v

namespace DecisionTree

variable {T : Type u} {Output : Type v}

/-- Querying a prescribed finite set suffices to evaluate any function on the
input obtained by setting all remaining coordinates to `false`. -/
theorem exists_read_finset [DecidableEq T] (s : Finset T) (f : (T → Bool) → Output) :
    ∃ tree : DecisionTree T Output,
      (∀ x, tree.eval x = f (fun i => if i ∈ s then x i else false)) ∧
      tree.depth ≤ s.card := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty =>
      exact ⟨.leaf (f (fun _ => false)), by simp [eval, depth]⟩
  | @insert i s hi ih =>
      obtain ⟨zero, hzero, dzero⟩ :=
        ih (fun x => f (fun j => if j = i then false else x j))
      obtain ⟨one, hone, done⟩ :=
        ih (fun x => f (fun j => if j = i then true else x j))
      refine ⟨.node i zero one, ?_, ?_⟩
      · intro x
        cases hx : x i <;> simp only [eval, hx, Bool.false_eq_true, ↓reduceIte]
        · rw [hzero]
          congr 1
          funext j
          by_cases hj : j = i
          · subst j
            simp [hi, hx]
          · simp [hj]
        · rw [hone]
          congr 1
          funext j
          by_cases hj : j = i
          · subst j
            simp [hi, hx]
          · simp [hj]
      · simp only [depth, Finset.card_insert_of_notMem hi]
        omega

/-- Every function on a finite Boolean input space has an exact tree that
queries at most the number of coordinates. -/
theorem exists_read_all [Fintype T] (f : (T → Bool) → Output) :
    ∃ tree : DecisionTree T Output,
      (∀ x, tree.eval x = f x) ∧ tree.depth ≤ Fintype.card T := by
  classical
  simpa using exists_read_finset (Finset.univ : Finset T) f

/-- A depth-zero tree has the same output on all inputs. -/
theorem eval_eq_of_depth_zero (tree : DecisionTree T Output)
    (h : tree.depth = 0) (x y : T → Bool) : tree.eval x = tree.eval y := by
  cases tree with
  | leaf answer => rfl
  | node i zero one => simp [depth] at h

end DecisionTree

variable {T : Type u} {f : BoolFn T} {d e : ℕ}

/-- Increasing the allowed number of queries preserves feasibility. -/
theorem HasRandomizedBound.mono (h : HasRandomizedBound f d) (hde : d ≤ e) :
    HasRandomizedBound f e := by
  rcases h with ⟨m, tree, weight, hdepth, hweight, hsum, hsuccess⟩
  exact ⟨m, tree, weight, fun i => (hdepth i).trans hde, hweight, hsum, hsuccess⟩

/-- An exact deterministic tree is also a randomized algorithm, by giving it
probability one. -/
theorem hasRandomizedBound_of_tree (tree : DecisionTree T Bool)
    (hcomputes : ∀ x, tree.eval x = f x) (hdepth : tree.depth ≤ d) :
    HasRandomizedBound f d := by
  refine ⟨1, fun _ => tree, fun _ => 1, fun _ => hdepth, ?_, ?_, ?_⟩ <;>
    norm_num [hcomputes]

/-- Reading the entire input is a feasible randomized query bound. -/
theorem hasRandomizedBound_card [Fintype T] (f : BoolFn T) :
    HasRandomizedBound f (Fintype.card T) := by
  obtain ⟨tree, hcomputes, hdepth⟩ := DecisionTree.exists_read_all f
  exact hasRandomizedBound_of_tree tree hcomputes hdepth

/-- The set whose infimum defines `R` is nonempty. -/
theorem randomizedBounds_nonempty [Fintype T] (f : BoolFn T) :
    {d : ℕ | HasRandomizedBound f d}.Nonempty :=
  ⟨Fintype.card T, hasRandomizedBound_card f⟩

/-- The least randomized query bound is attained. -/
theorem hasRandomizedBound_R [Fintype T] (f : BoolFn T) :
    HasRandomizedBound f (R f) :=
  Nat.sInf_mem (randomizedBounds_nonempty f)

/-- Any feasible query bound bounds `R` from above. -/
theorem R_le_of_hasRandomizedBound [Fintype T] (h : HasRandomizedBound f d) :
    R f ≤ d := Nat.sInf_le h

/-- Feasible query bounds are precisely the numbers at least `R`. -/
theorem hasRandomizedBound_iff_R_le [Fintype T] :
    HasRandomizedBound f d ↔ R f ≤ d :=
  ⟨R_le_of_hasRandomizedBound, fun h => (hasRandomizedBound_R f).mono h⟩

/-- Randomized query complexity is at most the number of input coordinates. -/
theorem R_le_card [Fintype T] (f : BoolFn T) : R f ≤ Fintype.card T :=
  R_le_of_hasRandomizedBound (hasRandomizedBound_card f)

/-- A zero-query randomized algorithm can compute only a constant function. -/
theorem constant_of_hasRandomizedBound_zero (h : HasRandomizedBound f 0) :
    ∃ b, ∀ x, f x = b := by
  classical
  rcases h with ⟨m, tree, weight, hdepth, hweight, hsum, hsuccess⟩
  have heval (i : Fin m) (x y : T → Bool) : (tree i).eval x = (tree i).eval y :=
    DecisionTree.eval_eq_of_depth_zero (tree i) (Nat.eq_zero_of_le_zero (hdepth i)) x y
  have hconstant (x y : T → Bool) : f x = f y := by
    by_contra hxy
    have hx := hsuccess x
    have hy := hsuccess y
    have hdisjoint :
        (∑ i, if (tree i).eval x = f x then weight i else 0) +
          (∑ i, if (tree i).eval y = f y then weight i else 0) ≤
            ∑ i, weight i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [heval i y x]
      split_ifs <;> grind
    linarith
  exact ⟨f (fun _ => false), fun x => hconstant x (fun _ => false)⟩

/-- Exactly the constant functions have randomized query complexity zero. -/
theorem R_eq_zero_iff_constant [Fintype T] (f : BoolFn T) :
    R f = 0 ↔ ∃ b, ∀ x, f x = b := by
  constructor
  · intro h
    exact constant_of_hasRandomizedBound_zero (h ▸ hasRandomizedBound_R f)
  · rintro ⟨b, hb⟩
    apply Nat.eq_zero_of_le_zero
    apply R_le_of_hasRandomizedBound
    exact hasRandomizedBound_of_tree (.leaf b) (fun x => (hb x).symm) (by rfl)

@[simp] theorem R_const [Fintype T] (b : Bool) : R (fun _ : T → Bool => b) = 0 :=
  (R_eq_zero_iff_constant _).2 ⟨b, fun _ => rfl⟩

/-- A nonconstant total Boolean function has positive randomized complexity. -/
theorem R_pos_of_nonconstant [Fintype T] (h : ∃ x y, f x ≠ f y) : 0 < R f := by
  grind [R_eq_zero_iff_constant]

/-- The product-coordinate definition evaluates the expected curried blocks. -/
@[simp] theorem comp_apply {T₁ : Type u} {T₂ : Type v}
    (f : BoolFn T₁) (g : BoolFn T₂) (x : T₁ × T₂ → Bool) :
    comp f g x = f (fun i => g (fun j => x (i, j))) := rfl

end QueryComplexity

namespace QueryComplexity

universe u v w

/-- Each target bit is either constant or a function of one source bit. -/
abbrev BitSubstitution (Source : Type u) (Target : Type v) :=
  Target → Bool ⊕ (Source × (Bool → Bool))

namespace BitSubstitution

def eval {Source : Type u} {Target : Type v}
    (σ : BitSubstitution Source Target) (x : Source → Bool) (j : Target) : Bool :=
  match σ j with
  | .inl b => b
  | .inr (i, value) => value (x i)

end BitSubstitution

namespace DecisionTree

variable {T : Type u} {U : Type v} {Output : Type w}

def mapOutput {Output' : Type*} (decode : Output → Output') :
    DecisionTree T Output → DecisionTree T Output'
  | .leaf answer => .leaf (decode answer)
  | .node i zero one => .node i (zero.mapOutput decode) (one.mapOutput decode)

@[simp] theorem eval_mapOutput {Output' : Type*} (decode : Output → Output')
    (tree : DecisionTree T Output) (x : T → Bool) :
    (tree.mapOutput decode).eval x = decode (tree.eval x) := by
  induction tree <;> simp_all [mapOutput, eval, apply_ite]

@[simp] theorem depth_mapOutput {Output' : Type*} (decode : Output → Output')
    (tree : DecisionTree T Output) : (tree.mapOutput decode).depth = tree.depth := by
  induction tree <;> simp_all [mapOutput, depth]

/-- Simulate a tree after substituting constants or single-bit functions. -/
def substitute (σ : BitSubstitution T U) : DecisionTree U Output → DecisionTree T Output
  | .leaf answer => .leaf answer
  | .node j zero one =>
      match σ j with
      | .inl b => if b then one.substitute σ else zero.substitute σ
      | .inr (i, value) =>
          .node i
            (if value false then one.substitute σ else zero.substitute σ)
            (if value true then one.substitute σ else zero.substitute σ)

@[simp] theorem eval_substitute (σ : BitSubstitution T U)
    (tree : DecisionTree U Output) (x : T → Bool) :
    (tree.substitute σ).eval x = tree.eval (σ.eval x) := by
  induction tree with
  | leaf answer => rfl
  | node j zero one hz ho =>
      cases hs : σ j with
      | inl b => cases b <;> simp [substitute, hs, eval, BitSubstitution.eval, hz, ho]
      | inr pair =>
          obtain ⟨i, value⟩ := pair
          cases hx : x i <;>
            cases h0 : value false <;> cases h1 : value true <;>
            simp [substitute, hs, eval, BitSubstitution.eval, hx, h0, h1, hz, ho]

theorem depth_substitute_le (σ : BitSubstitution T U) (tree : DecisionTree U Output) :
    (tree.substitute σ).depth ≤ tree.depth := by
  induction tree with
  | leaf answer => rfl
  | node j zero one hz ho =>
      cases hs : σ j with
      | inl b => cases b <;> simp [substitute, hs, depth] <;> omega
      | inr pair =>
          obtain ⟨i, value⟩ := pair
          cases h0 : value false <;> cases h1 : value true <;>
            simp [substitute, hs, depth, h0, h1] <;> omega

end DecisionTree

variable {T : Type u} {U : Type v}

/-- A substitution and output decoder simulate a target randomized algorithm
without increasing its depth or error. -/
theorem HasRandomizedBound.of_reduction {f : BoolFn U} {g : BoolFn T} {d : ℕ}
    (h : HasRandomizedBound f d) (σ : BitSubstitution T U) (decode : Bool → Bool)
    (hcorrect : ∀ x, decode (f (σ.eval x)) = g x) : HasRandomizedBound g d := by
  classical
  rcases h with ⟨m, tree, weight, hdepth, hweight, hsum, hsuccess⟩
  refine ⟨m, fun i => ((tree i).substitute σ).mapOutput decode, weight, ?_,
    hweight, hsum, ?_⟩
  · intro i
    simpa using ((tree i).depth_substitute_le σ).trans (hdepth i)
  · intro x
    apply (hsuccess (σ.eval x)).trans
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [DecisionTree.eval_mapOutput, DecisionTree.eval_substitute]
    by_cases hi : (tree i).eval (σ.eval x) = f (σ.eval x)
    · simp [hi, hcorrect]
    · simp only [hi, ↓reduceIte]
      split_ifs <;> simp [hweight]

/-- Query complexity is monotone under single-bit input reductions. -/
theorem R_le_of_reduction [Fintype T] [Fintype U] {f : BoolFn U} {g : BoolFn T}
    (σ : BitSubstitution T U) (decode : Bool → Bool)
    (hcorrect : ∀ x, decode (f (σ.eval x)) = g x) : R g ≤ R f :=
  R_le_of_hasRandomizedBound ((hasRandomizedBound_R f).of_reduction σ decode hcorrect)

/-- Transport a function to an equivalent coordinate type. -/
def reindex (e : T ≃ U) (f : BoolFn T) : BoolFn U :=
  fun x => f (fun i => x (e i))

@[simp] theorem reindex_apply (e : T ≃ U) (f : BoolFn T) (x : U → Bool) :
    reindex e f x = f (fun i => x (e i)) := rfl

@[simp] theorem reindex_symm (e : T ≃ U) (f : BoolFn T) :
    reindex e.symm (reindex e f) = f := by
  funext x
  simp [reindex]

theorem R_reindex_le [Fintype T] [Fintype U] (e : T ≃ U) (f : BoolFn T) :
    R (reindex e f) ≤ R f := by
  apply R_le_of_reduction (fun i => .inr (e i, id)) id
  intro x
  rfl

/-- Relabeling coordinates preserves randomized query complexity. -/
@[simp] theorem R_reindex [Fintype T] [Fintype U] (e : T ≃ U) (f : BoolFn T) :
    R (reindex e f) = R f := by
  apply le_antisymm (R_reindex_le e f)
  simpa using R_reindex_le e.symm (reindex e f)

/-- Independent coordinate changes of the factors are the product coordinate
change of their block composition. -/
theorem comp_reindex {T' : Type*} {U' : Type*}
    (e : T ≃ T') (e' : U ≃ U') (f : BoolFn T) (g : BoolFn U) :
    comp (reindex e f) (reindex e' g) = reindex (e.prodCongr e') (comp f g) := rfl

@[simp] theorem R_comp_reindex [Fintype T] [Fintype U]
    {T' : Type*} {U' : Type*} [Fintype T'] [Fintype U']
    (e : T ≃ T') (e' : U ≃ U') (f : BoolFn T) (g : BoolFn U) :
    R (comp (reindex e f) (reindex e' g)) = R (comp f g) := by
  rw [comp_reindex, R_reindex]

/-- Put a function on `Fin` coordinates without changing its query complexity. -/
noncomputable def toFin [Fintype T] (f : BoolFn T) : BoolFn (Fin (Fintype.card T)) :=
  reindex (Fintype.equivFin T) f

@[simp] theorem R_toFin [Fintype T] (f : BoolFn T) : R (toFin f) = R f :=
  R_reindex _ _

@[simp] theorem R_comp_toFin [Fintype T] [Fintype U] (f : BoolFn T) (g : BoolFn U) :
    R (comp (toFin f) (toFin g)) = R (comp f g) :=
  R_comp_reindex _ _ _ _

/-- A nonconstant Boolean function attains both Boolean values. -/
theorem exists_false_true_of_nonconstant {f : BoolFn T}
    (h : ∃ x y, f x ≠ f y) : ∃ x₀ x₁, f x₀ = false ∧ f x₁ = true := by
  obtain ⟨x, y, hxy⟩ := h
  cases hx : f x <;> cases hy : f y
  · exact (hxy (hx.trans hy.symm)).elim
  · exact ⟨x, y, hx, hy⟩
  · exact ⟨y, x, hy, hx⟩
  · exact (hxy (hx.trans hy.symm)).elim

/-- A nonconstant function on a finite Boolean cube changes across some edge. -/
theorem exists_sensitive_coordinate [Fintype T] [DecidableEq T] {f : BoolFn T}
    (h : ∃ x y, f x ≠ f y) :
    ∃ x i, f (Function.update x i false) ≠ f (Function.update x i true) := by
  by_contra! hedge
  have hupdate (x : T → Bool) (i : T) (b : Bool) :
      f (Function.update x i b) = f x := by
    have hself : f (Function.update x i (x i)) = f x := by
      rw [Function.update_eq_self]
    apply Eq.trans ?_ hself
    cases b <;> cases x i
    · rfl
    · exact hedge x i
    · exact (hedge x i).symm
    · rfl
  have hfinite (s : Finset T) (x y : T → Bool) :
      f (fun i => if i ∈ s then y i else x i) = f x := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        have heq : (fun j => if j ∈ insert i s then y j else x j) =
            Function.update (fun j => if j ∈ s then y j else x j) i (y i) := by
          funext j
          by_cases hj : j = i
          · subst j
            simp
          · simp [hj]
        rw [heq, hupdate]
        exact ih
  obtain ⟨x, y, hxy⟩ := h
  apply hxy
  symm
  simpa using hfinite Finset.univ x y

/-- A nonconstant inner function lets us encode each outer input bit in a
block, so the composition is at least as hard as the outer function. -/
theorem R_outer_le_comp [Fintype T] [Fintype U] (f : BoolFn T) (g : BoolFn U)
    (hg : ∃ x y, g x ≠ g y) : R f ≤ R (comp f g) := by
  obtain ⟨x₀, x₁, hg₀, hg₁⟩ := exists_false_true_of_nonconstant hg
  let σ : BitSubstitution T (T × U) :=
    fun ij => .inr (ij.1, fun b => if b then x₁ ij.2 else x₀ ij.2)
  refine R_le_of_reduction σ id fun x => ?_
  simp only [comp_apply, id_eq]
  refine congrArg f (funext fun i => ?_)
  cases hx : x i <;> simp [σ, BitSubstitution.eval, hx, hg₀, hg₁]

/-- Fix all but one sensitive outer coordinate and decode its two possible
outputs. This reduces the inner function to the composition. -/
theorem R_inner_le_comp [Fintype T] [Fintype U] (f : BoolFn T) (g : BoolFn U)
    (hf : ∃ x y, f x ≠ f y) (hg : ∃ x y, g x ≠ g y) :
    R g ≤ R (comp f g) := by
  classical
  obtain ⟨z, i, hi⟩ := exists_sensitive_coordinate hf
  obtain ⟨x₀, x₁, hg₀, hg₁⟩ := exists_false_true_of_nonconstant hg
  let σ : BitSubstitution U (T × U) := fun ij =>
    if ij.1 = i then .inr (ij.2, id)
    else .inl (if z ij.1 then x₁ ij.2 else x₀ ij.2)
  let decode : Bool → Bool :=
    fun b => if b = f (Function.update z i false) then false else true
  refine R_le_of_reduction σ decode fun x => ?_
  have hblocks : (fun j => g (fun k => σ.eval x (j, k))) =
      Function.update z i (g x) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [σ, BitSubstitution.eval]
    · cases hz : z j <;>
        simp [σ, BitSubstitution.eval, hj, hz, hg₀, hg₁]
  rw [comp_apply, hblocks]
  cases g x <;> simp [decode, hi.symm]

/-- The composed function is nonconstant whenever both factors are. -/
theorem R_comp_pos [Fintype T] [Fintype U] (f : BoolFn T) (g : BoolFn U)
    (hf : ∃ x y, f x ≠ f y) (hg : ∃ x y, g x ≠ g y) : 0 < R (comp f g) :=
  (R_pos_of_nonconstant hf).trans_le (R_outer_le_comp f g hg)

end QueryComplexity
