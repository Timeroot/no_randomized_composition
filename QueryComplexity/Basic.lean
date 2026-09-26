import QueryComplexity.Definitions
import Mathlib.Tactic

/-!
# Basic facts about the randomized query model

These proofs establish feasibility, attainment of the natural-number minimum,
and the characterization of zero complexity, for arbitrary finite coordinate
types. No query-complexity lower-bound theorem is assumed.
-/

open scoped BigOperators

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
  refine ⟨1, fun _ => tree, fun _ => 1, fun _ => hdepth, ?_, ?_, ?_⟩
  · intro i
    norm_num
  · simp
  · intro x
    simp [hcomputes]
    norm_num

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
      apply Finset.sum_le_sum
      intro i _
      rw [heval i y x]
      split_ifs with hix hiy hiy
      · exact (hxy (hix.symm.trans hiy)).elim
      · simp
      · simp
      · simpa using hweight i
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
  apply Nat.pos_of_ne_zero
  intro hzero
  obtain ⟨b, hb⟩ := (R_eq_zero_iff_constant f).1 hzero
  obtain ⟨x, y, hxy⟩ := h
  exact hxy ((hb x).trans (hb y).symm)

/-- The product-coordinate definition evaluates the expected curried blocks. -/
@[simp] theorem comp_apply {T₁ : Type u} {T₂ : Type v}
    (f : BoolFn T₁) (g : BoolFn T₂) (x : T₁ × T₂ → Bool) :
    comp f g x = f (fun i => g (fun j => x (i, j))) := rfl

end QueryComplexity
