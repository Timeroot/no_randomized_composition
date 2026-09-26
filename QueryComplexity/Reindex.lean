import QueryComplexity.Basic

/-!
# Coordinate changes and restrictions

A query reduction may replace each target coordinate by a constant or by a
function of one source bit. It may also decode the Boolean output. Such a
reduction does not increase randomized query complexity.
-/

open scoped BigOperators

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
  induction tree with
  | leaf answer => rfl
  | node i zero one hz ho => cases hx : x i <;> simp [mapOutput, eval, hx, hz, ho]

@[simp] theorem depth_mapOutput {Output' : Type*} (decode : Output → Output')
    (tree : DecisionTree T Output) : (tree.mapOutput decode).depth = tree.depth := by
  induction tree with
  | leaf answer => rfl
  | node i zero one hz ho => simp [mapOutput, depth, hz, ho]

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
    apply Finset.sum_le_sum
    intro i _
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
  apply R_le_of_reduction σ id
  intro x
  change f (fun i => g (fun j => σ.eval x (i, j))) = f x
  congr 1
  funext i
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
  apply R_le_of_reduction σ decode
  intro x
  have hblocks : (fun j => g (fun k => σ.eval x (j, k))) =
      Function.update z i (g x) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [σ, BitSubstitution.eval]
    · cases hz : z j <;>
        simp [σ, BitSubstitution.eval, hj, hz, hg₀, hg₁]
  change decode (f (fun j => g (fun k => σ.eval x (j, k)))) = g x
  rw [hblocks]
  cases g x <;> simp [decode, hi.symm]

/-- The composed function is nonconstant whenever both factors are. -/
theorem R_comp_pos [Fintype T] [Fintype U] (f : BoolFn T) (g : BoolFn U)
    (hf : ∃ x y, f x ≠ f y) (hg : ∃ x y, g x ≠ g y) : 0 < R (comp f g) :=
  (R_pos_of_nonconstant hf).trans_le (R_outer_le_comp f g hg)

end QueryComplexity
