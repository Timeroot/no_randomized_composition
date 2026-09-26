import QueryComplexity.DecisionTree.Cost
import QueryComplexity.LowerBounds.DirectProduct
import Mathlib.Data.Fintype.EquivFin

/-! A query tree can record the cells it queried more than a threshold number
of times and return a fixed-length array containing every such cell. -/

open scoped BigOperators

namespace QueryComplexity.DecisionTree

universe u v w

variable {T : Type u} {Output : Type v} {A : Type w} [DecidableEq A]

def ownerCount (owner : T → Option A) (tree : DecisionTree T Output) (a : A) (x : T → Bool) : ℕ :=
  tree.queryCount (fun j => decide (owner j = some a)) x

def incrementOwner (s : A → ℕ) : Option A → A → ℕ
  | none => s
  | some a => Function.update s a (s a + 1)

theorem incrementOwner_apply (s : A → ℕ) (o : Option A) (a : A) :
    incrementOwner s o a = s a + if o = some a then 1 else 0 := by
  cases o with
  | none => simp [incrementOwner]
  | some b =>
    by_cases ha : a = b
    · subst a
      simp [incrementOwner]
    · simp [incrementOwner, ha, Ne.symm ha]

def recordCounts (owner : T → Option A) (s : A → ℕ) :
    DecisionTree T Output → DecisionTree T (A → ℕ)
  | .leaf _ => .leaf s
  | .node j zero one => .node j
      (recordCounts owner (incrementOwner s (owner j)) zero)
      (recordCounts owner (incrementOwner s (owner j)) one)

@[simp] theorem depth_recordCounts (owner : T → Option A) (s : A → ℕ)
    (tree : DecisionTree T Output) : (recordCounts owner s tree).depth = tree.depth := by
  induction tree generalizing s with
  | leaf answer => rfl
  | node j zero one ihz iho => simp [recordCounts, depth, ihz, iho]

theorem eval_recordCounts (owner : T → Option A) (s : A → ℕ)
    (tree : DecisionTree T Output) (x : T → Bool) :
    (recordCounts owner s tree).eval x = fun a => s a + ownerCount owner tree a x := by
  induction tree generalizing s with
  | leaf answer => rfl
  | node j zero one ihz iho =>
    by_cases hx : x j = true
    · simp only [recordCounts, eval, hx, if_true, iho]
      funext a
      rw [incrementOwner_apply]
      simp [ownerCount, queryCount, hx, Nat.add_assoc]
    · have hf : x j = false := Bool.eq_false_of_not_eq_true hx
      simp only [recordCounts, eval, hf, Bool.false_eq_true, if_false, ihz]
      funext a
      rw [incrementOwner_apply]
      simp [ownerCount, queryCount, hf, Nat.add_assoc]

section Finite

variable [Fintype A]

theorem sum_ownerCount_le_cost (owner : T → Option A) (tree : DecisionTree T Output)
    (x : T → Bool) : (∑ a, ownerCount owner tree a x) ≤ tree.queryCost x := by
  induction tree with
  | leaf answer => simp [ownerCount, queryCount, queryCost]
  | node j zero one ihz iho =>
    simp only [ownerCount] at ihz iho
    simp only [ownerCount, queryCount, queryCost, Finset.sum_add_distrib]
    have ho : (∑ a : A, if decide (owner j = some a) then 1 else 0) ≤ 1 := by
      cases owner j <;> simp
    by_cases hx : x j = true
    · simp only [hx, if_true]
      exact Nat.add_le_add ho iho
    · have hf : x j = false := Bool.eq_false_of_not_eq_true hx
      simp only [hf, Bool.false_eq_true, if_false]
      exact Nat.add_le_add ho ihz

def heavySet (threshold : ℕ) (s : A → ℕ) : Finset A :=
  Finset.univ.filter (fun a => threshold < s a)

omit [DecidableEq A] in
theorem heavySet_card (threshold : ℕ) (s : A → ℕ) :
    (heavySet threshold s).card = DirectProduct.heavyCount threshold s := by
  simp only [heavySet, DirectProduct.heavyCount, Finset.card_filter]

def heavyRecorder (owner : T → Option A) (threshold : ℕ) (tree : DecisionTree T Output) :
    DecisionTree T (Finset A) :=
  (recordCounts owner (fun _ => 0) tree).mapOutput (heavySet threshold)

@[simp] theorem depth_heavyRecorder (owner : T → Option A) (threshold : ℕ)
    (tree : DecisionTree T Output) : (heavyRecorder owner threshold tree).depth = tree.depth := by
  simp [heavyRecorder]

theorem eval_heavyRecorder (owner : T → Option A) (threshold : ℕ)
    (tree : DecisionTree T Output) (x : T → Bool) :
    (heavyRecorder owner threshold tree).eval x = heavySet threshold (fun a => ownerCount owner tree a x) := by
  simp [heavyRecorder, eval_recordCounts]

theorem heavyRecorder_card_le (owner : T → Option A) (threshold Q : ℕ)
    (tree : DecisionTree T Output) (hdepth : tree.depth ≤ Q) (x : T → Bool) :
    ((heavyRecorder owner threshold tree).eval x).card ≤ Q / (threshold + 1) := by
  rw [eval_heavyRecorder, heavySet_card]
  apply DirectProduct.heavyCount_le_div
  exact (sum_ownerCount_le_cost owner tree x).trans ((queryCost_le_depth tree x).trans hdepth)

theorem heavyRecorder_contains (owner : T → Option A) (threshold : ℕ)
    (tree : DecisionTree T Output) (x : T → Bool) (a : A)
    (h : threshold < ownerCount owner tree a x) :
    a ∈ (heavyRecorder owner threshold tree).eval x := by
  simp [eval_heavyRecorder, heavySet, h]

noncomputable def padFinset (fallback : A) (L : ℕ) (s : Finset A) : Fin L → A :=
  fun j => if h : j.val < s.card then (s.equivFin.symm ⟨j.val, h⟩).val else fallback

omit [DecidableEq A] [Fintype A] in
theorem padFinset_covers (fallback : A) (L : ℕ) (s : Finset A) (a : A)
    (hcard : s.card ≤ L) (ha : a ∈ s) : ∃ j : Fin L, padFinset fallback L s j = a := by
  let j := s.equivFin ⟨a, ha⟩
  refine ⟨⟨j.val, lt_of_lt_of_le j.isLt hcard⟩, ?_⟩
  simp only [padFinset, dif_pos j.isLt, j, Fin.eta, Equiv.symm_apply_apply]

noncomputable def heavyListTree (owner : T → Option A) (threshold L : ℕ) (fallback : A)
    (tree : DecisionTree T Output) : DecisionTree T (Fin L → A) :=
  (heavyRecorder owner threshold tree).mapOutput (padFinset fallback L)

@[simp] theorem depth_heavyListTree (owner : T → Option A) (threshold L : ℕ) (fallback : A)
    (tree : DecisionTree T Output) : (heavyListTree owner threshold L fallback tree).depth = tree.depth := by
  simp [heavyListTree]

/-- Every cell whose local cost exceeds the threshold appears in the returned
array. Querying the array-producing tree costs exactly the original depth. -/
theorem heavyListTree_contains (owner : T → Option A) (threshold L Q : ℕ) (fallback : A)
    (tree : DecisionTree T Output) (hdepth : tree.depth ≤ Q)
    (hL : Q / (threshold + 1) ≤ L) (x : T → Bool) (a : A)
    (ha : threshold < ownerCount owner tree a x) :
    ∃ j : Fin L, (heavyListTree owner threshold L fallback tree).eval x j = a := by
  have hc := (heavyRecorder_card_le owner threshold Q tree hdepth x).trans hL
  have hm := heavyRecorder_contains owner threshold tree x a ha
  simpa only [heavyListTree, eval_mapOutput] using
    padFinset_covers fallback L ((heavyRecorder owner threshold tree).eval x) a hc hm

end Finite

end QueryComplexity.DecisionTree
