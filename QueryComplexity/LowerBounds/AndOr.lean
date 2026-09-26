import QueryComplexity.DecisionTree.Cost
import ForMathlib.Probability.FiniteProbability

open scoped BigOperators

namespace QueryComplexity.AndOrLower

variable {T Output : Type*} [DecidableEq T]

def oneHot (i : T) : T → Bool := fun j => decide (j = i)

/-- Whether the search encounters the unique one. After the encounter the
remainder of the tree is irrelevant to this event. -/
def hits : DecisionTree T Output → T → Bool
  | .leaf _, _ => false
  | .node j zero _, i => if i = j then true else hits zero i

def hitCount (s : Finset T) (tree : DecisionTree T Output) : ℕ :=
  (s.filter (fun i => hits tree i = true)).card

theorem hitCount_le (s : Finset T) (tree : DecisionTree T Output) :
    hitCount s tree ≤ s.card := Finset.card_filter_le _ _

theorem hitCount_node (s : Finset T) (j : T) (zero one : DecisionTree T Output) :
    hitCount s (.node j zero one) =
      if j ∈ s then 1 + hitCount (s.erase j) zero else hitCount s zero := by
  classical
  by_cases hj : j ∈ s
  · rw [if_pos hj]
    have he : s.filter (fun i => hits (.node j zero one) i = true) =
        insert j ((s.erase j).filter (fun i => hits zero i = true)) := by
      ext i
      by_cases hi : i = j <;> simp [hits, hi, hj]
    unfold hitCount
    rw [he, Finset.card_insert_of_notMem (by simp)]
    omega
  · rw [if_neg hj]
    unfold hitCount
    congr 1
    ext i
    by_cases hi : i = j <;> simp [hits, hi, hj]

theorem node_cost_lower (s : Finset T) (j : T) (zero one : DecisionTree T Output) :
    s.card + (∑ i ∈ s.erase j, zero.queryCost (oneHot i)) ≤
      ∑ i ∈ s, (DecisionTree.node j zero one).queryCost (oneHot i) := by
  have he : (∑ i ∈ s, (DecisionTree.node j zero one).queryCost (oneHot i)) =
      s.card + ∑ i ∈ s,
        (if i = j then one.queryCost (oneHot i) else zero.queryCost (oneHot i)) := by
    simp [DecisionTree.queryCost, oneHot, eq_comm, Finset.sum_add_distrib]
  rw [he]
  apply Nat.add_le_add_left
  calc
    (∑ i ∈ s.erase j, zero.queryCost (oneHot i)) =
        ∑ i ∈ s.erase j,
          (if i = j then one.queryCost (oneHot i) else zero.queryCost (oneHot i)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [if_neg (Finset.mem_erase.mp hi).1]
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)

/-- Uniform search for a hidden location: twice the expected number of
queries bounds the number of possible locations times the hit probability.
The statement allows arbitrary adaptive stopping and repeated queries. -/
theorem search_cost_bound (tree : DecisionTree T Output) (s : Finset T) :
    s.card * hitCount s tree ≤ 2 * ∑ i ∈ s, tree.queryCost (oneHot i) := by
  induction tree generalizing s with
  | leaf answer => simp [hitCount, hits, DecisionTree.queryCost]
  | node j zero one ihz iho =>
    have hc := node_cost_lower s j zero one
    rw [hitCount_node]
    by_cases hj : j ∈ s
    · rw [if_pos hj]
      have hi := ihz (s.erase j)
      have hh := hitCount_le (s.erase j) zero
      have hs : (s.erase j).card + 1 = s.card := Finset.card_erase_add_one hj
      nlinarith
    · rw [if_neg hj]
      rw [Finset.erase_eq_of_notMem hj] at hc
      have hi := ihz s
      omega

theorem eval_eq_zero_of_no_hit (tree : DecisionTree T Output) (i : T)
    (h : hits tree i = false) : tree.eval (oneHot i) = tree.eval (fun _ => false) := by
  induction tree with
  | leaf answer => rfl
  | node j zero one ihz iho =>
    have hij : i ≠ j := by
      intro hij
      simp [hits, hij] at h
    have hz : hits zero i = false := by simpa [hits, hij] using h
    simpa [DecisionTree.eval, oneHot, Ne.symm hij] using ihz hz

section Rows

variable {I : Type*} [Fintype I] [DecidableEq I] [Fintype T]

def positive (a : I → T) : I × T → Bool := fun p => oneHot (a p.1) p.2

def negative (a : I → T) (i : I) : I × T → Bool :=
  DecisionTree.replaceBlock i (positive a) (fun _ => false)

def rowTree (tree : DecisionTree (I × T) Output) (i : I) (a : I → T) :
    DecisionTree T Output := tree.projectBlock i (positive a)

def rowHit (tree : DecisionTree (I × T) Output) (i : I) (a : I → T) : ℕ :=
  if hits (rowTree tree i a) (a i) then 1 else 0

omit [Fintype T] [Fintype I] in
theorem replace_positive (a : I → T) (i : I) :
    DecisionTree.replaceBlock i (positive a) (oneHot (a i)) = positive a :=
  DecisionTree.replaceBlock_self i (positive a)

omit [Fintype I] [Fintype T] in
theorem rowTree_update (tree : DecisionTree (I × T) Output) (i : I) (a : I → T) (t : T) :
    rowTree tree i (Function.update a i t) = rowTree tree i a := by
  unfold rowTree DecisionTree.projectBlock
  congr 1
  funext p
  by_cases hp : p.1 = i
  · simp [DecisionTree.blockSubstitution, hp]
  · simp [DecisionTree.blockSubstitution, hp, positive]

omit [Fintype I] [Fintype T] in
theorem rowHit_update (tree : DecisionTree (I × T) Output) (i : I) (a : I → T) (t : T) :
    rowHit tree i (Function.update a i t) = if hits (rowTree tree i a) t then 1 else 0 := by
  simp [rowHit, rowTree_update]

omit [Fintype T] [Fintype I] in
theorem row_cost (tree : DecisionTree (I × T) Output) (i : I) (a : I → T) :
    (rowTree tree i a).queryCost (oneHot (a i)) = tree.blockCost i (positive a) := by
  rw [rowTree, DecisionTree.cost_projectBlock, replace_positive]

omit [Fintype T] [Fintype I] in
theorem row_cost_update (tree : DecisionTree (I × T) Output) (i : I) (a : I → T) (t : T) :
    tree.blockCost i (positive (Function.update a i t)) =
      (rowTree tree i a).queryCost (oneHot t) := by
  rw [← row_cost, rowTree_update]
  simp

theorem sum_rowHit_le_cost [Nonempty T]
    (tree : DecisionTree (I × T) Output) (i : I) :
    Fintype.card T * (∑ a : I → T, rowHit tree i a) ≤
      2 * ∑ a : I → T, tree.blockCost i (positive a) := by
  have hp (a : I → T) :
      Fintype.card T * (∑ t : T, rowHit tree i (Function.update a i t)) ≤
        2 * ∑ t : T, tree.blockCost i (positive (Function.update a i t)) := by
    simp_rw [rowHit_update, row_cost_update]
    simpa only [hitCount, Finset.card_filter, Finset.card_univ] using
      search_cost_bound (rowTree tree i a) Finset.univ
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hp a)
  simp only [← Finset.mul_sum] at hs
  rw [FiniteProbability.sum_resample i (fun a => rowHit tree i a),
    FiniteProbability.sum_resample i (fun a => tree.blockCost i (positive a))] at hs
  have hs' : Fintype.card T * (Fintype.card T * ∑ a : I → T, rowHit tree i a) ≤
      Fintype.card T * (2 * ∑ a : I → T, tree.blockCost i (positive a)) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hs
  exact Nat.le_of_mul_le_mul_left hs' Fintype.card_pos

theorem sum_all_hits_le_cost [Nonempty T] (tree : DecisionTree (I × T) Output) :
    Fintype.card T * (∑ a : I → T, ∑ i : I, rowHit tree i a) ≤
      2 * ∑ a : I → T, tree.queryCost (positive a) := by
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => sum_rowHit_le_cost tree i)
  simp only [← Finset.mul_sum] at hs
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i a => tree.blockCost i (positive a))] at hs
  simpa only [DecisionTree.sum_blockCost] using hs

omit [Fintype T] [Fintype I] in
theorem positive_negative_agree_of_no_hit (tree : DecisionTree (I × T) Output)
    (i : I) (a : I → T) (h : hits (rowTree tree i a) (a i) = false) :
    tree.eval (positive a) = tree.eval (negative a i) := by
  have he := eval_eq_zero_of_no_hit (rowTree tree i a) (a i) h
  simpa only [rowTree, DecisionTree.eval_projectBlock, replace_positive, negative] using he

omit [Fintype T] [Fintype I] in
theorem coupled_success_bound (tree : DecisionTree (I × T) Bool) (a : I → T) (i : I) :
    (if tree.eval (positive a) = true then 1 else 0) +
        (if tree.eval (negative a i) = false then 1 else 0) ≤ 1 + rowHit tree i a := by
  cases hh : hits (rowTree tree i a) (a i)
  · have he := positive_negative_agree_of_no_hit tree i a hh
    rw [he]
    cases tree.eval (negative a i) <;> simp [rowHit, hh]
  · simp only [rowHit, hh, if_true]
    split_ifs <;> omega

/-- The explicit AND--OR hard distribution: each row has a uniformly hidden
one on positive inputs; a uniformly selected row loses its one on negatives.
This unnormalized inequality bounds success using expected positive-input
cost, and applies to arbitrary adaptive stopping. -/
theorem andOr_success_cost_bound [Nonempty T] (tree : DecisionTree (I × T) Bool) :
    Fintype.card T *
      (∑ a : I → T, ∑ i : I,
        ((if tree.eval (positive a) = true then 1 else 0) +
          (if tree.eval (negative a i) = false then 1 else 0))) ≤
      Fintype.card T * (Fintype.card (I → T) * Fintype.card I) +
        2 * ∑ a : I → T, tree.queryCost (positive a) := by
  have hp := Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun i _ => coupled_success_bound tree a i))
  have hmul := Nat.mul_le_mul_left (Fintype.card T) hp
  have hh := sum_all_hits_le_cost tree
  have he : (∑ a : I → T, ∑ i : I, (1 + rowHit tree i a)) =
      Fintype.card (I → T) * Fintype.card I + ∑ a : I → T, ∑ i : I, rowHit tree i a := by
    simp [Finset.sum_add_distrib]
  rw [he, Nat.mul_add] at hmul
  exact hmul.trans (Nat.add_le_add_left hh _)

def scenario (a : I → T) (i : I) (b : Bool) : I × T → Bool :=
  if b then positive a else negative a i

theorem average_eq_sum_div {X : Type*} [Fintype X] (f : X → ℝ) :
    FiniteProbability.average f = (∑ x, f x) / (Fintype.card X : ℝ) := by
  unfold FiniteProbability.average FiniteProbability.uniformWeight
  rw [← Finset.mul_sum]
  ring

omit [Fintype I] [Fintype T] in
theorem average_scenario_bool (tree : DecisionTree (I × T) Bool) (a : I → T) (i : I) :
    FiniteProbability.average (fun b : Bool =>
      if tree.eval (scenario a i b) = b then (1 : ℝ) else 0) =
    ((if tree.eval (positive a) = true then (1 : ℝ) else 0) +
      (if tree.eval (negative a i) = false then (1 : ℝ) else 0)) / 2 := by
  rw [average_eq_sum_div]
  simp only [Fintype.sum_bool, Fintype.card_bool, Nat.cast_ofNat, scenario,
    Bool.false_eq_true, ↓reduceIte]

theorem andOr_average_success_bound [Nonempty I] [Nonempty T]
    (tree : DecisionTree (I × T) Bool) :
    FiniteProbability.average (fun a : I → T =>
      FiniteProbability.average (fun i : I =>
        FiniteProbability.average (fun b : Bool =>
          if tree.eval (scenario a i b) = b then (1 : ℝ) else 0))) ≤
      1 / 2 + FiniteProbability.average (fun a : I → T => (tree.queryCost (positive a) : ℝ)) /
        ((Fintype.card I : ℝ) * (Fintype.card T : ℝ)) := by
  have hreal : (Fintype.card T : ℝ) *
      (∑ a : I → T, ∑ i : I,
        ((if tree.eval (positive a) = true then (1 : ℝ) else 0) +
          (if tree.eval (negative a i) = false then (1 : ℝ) else 0))) ≤
      (Fintype.card T : ℝ) * ((Fintype.card (I → T) : ℝ) * Fintype.card I) +
        2 * ∑ a : I → T, (tree.queryCost (positive a) : ℝ) := by
    exact_mod_cast andOr_success_cost_bound tree
  have ha : (0 : ℝ) < Fintype.card (I → T) := by exact_mod_cast Fintype.card_pos
  have hi : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have ht : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  simp_rw [average_scenario_bool, average_eq_sum_div, ← Finset.sum_div]
  have hs := div_le_div_of_nonneg_right hreal
    (show 0 ≤ 2 * (Fintype.card (I → T) : ℝ) * Fintype.card I * Fintype.card T by positivity)
  convert hs using 1 <;> field_simp

end Rows

end QueryComplexity.AndOrLower
