import QueryComplexity.Basic

/-! Actual path costs, truncation, and restriction to a single input block.
These are properties of the same concrete decision trees used to define `R`. -/

open scoped BigOperators

namespace QueryComplexity.DecisionTree

universe u v w

variable {T : Type u} {Output : Type v}

def queryCost : DecisionTree T Output → (T → Bool) → ℕ
  | .leaf _, _ => 0
  | .node j zero one, x => 1 + if x j then queryCost one x else queryCost zero x

def queryCount (p : T → Bool) : DecisionTree T Output → (T → Bool) → ℕ
  | .leaf _, _ => 0
  | .node j zero one, x => (if p j then 1 else 0) +
      if x j then queryCount p one x else queryCount p zero x

theorem queryCost_le_depth (tree : DecisionTree T Output) (x : T → Bool) :
    tree.queryCost x ≤ tree.depth := by
  induction tree with
  | leaf answer => rfl
  | node j zero one ihz iho =>
    simp only [queryCost, depth]
    split_ifs <;> omega

theorem queryCount_le_queryCost (p : T → Bool) (tree : DecisionTree T Output) (x : T → Bool) :
    tree.queryCount p x ≤ tree.queryCost x := by
  induction tree with
  | leaf answer => rfl
  | node j zero one ihz iho =>
    simp only [queryCost, queryCount]
    split_ifs <;> omega

def truncate (fallback : Output) : ℕ → DecisionTree T Output → DecisionTree T Output
  | 0, _ => .leaf fallback
  | _ + 1, .leaf answer => .leaf answer
  | d + 1, .node j zero one => .node j (truncate fallback d zero) (truncate fallback d one)

theorem depth_truncate_le (fallback : Output) (d : ℕ) (tree : DecisionTree T Output) :
    (tree.truncate fallback d).depth ≤ d := by
  induction d generalizing tree with
  | zero => rfl
  | succ d ih =>
    cases tree with
    | leaf answer => simp [truncate, depth]
    | node j zero one =>
      simp only [truncate, depth]
      have hz := ih zero
      have ho := ih one
      omega

theorem eval_truncate_of_cost_lt (fallback : Output) (d : ℕ)
    (tree : DecisionTree T Output) (x : T → Bool) (h : tree.queryCost x < d) :
    (tree.truncate fallback d).eval x = tree.eval x := by
  induction d generalizing tree with
  | zero => omega
  | succ d ih =>
    cases tree with
    | leaf answer => rfl
    | node j zero one =>
      simp only [queryCost] at h
      simp only [truncate, eval]
      split_ifs with hx
      · apply ih one
        simp only [hx, if_true] at h
        omega
      · apply ih zero
        simp only [hx, Bool.false_eq_true, if_false] at h
        omega

theorem queryCost_substitute {U : Type w} (σ : BitSubstitution T U)
    (tree : DecisionTree U Output) (x : T → Bool) :
    (tree.substitute σ).queryCost x =
      tree.queryCount (fun j => (σ j).isRight) (σ.eval x) := by
  induction tree with
  | leaf answer => rfl
  | node j zero one ihz iho =>
    cases hs : σ j with
    | inl b =>
      cases b <;> simp [substitute, queryCount, BitSubstitution.eval, hs, ihz, iho]
    | inr p =>
      rcases p with ⟨i, value⟩
      cases hx : x i <;> cases hv : value false <;> cases hw : value true <;>
        simp [substitute, queryCost, queryCount, BitSubstitution.eval, hs, hx, hv, hw, ihz, iho]

section Blocks

variable {I : Type w} [Fintype I] [DecidableEq I]

def blockCost (tree : DecisionTree (I × T) Output) (i : I) (x : I × T → Bool) : ℕ :=
  tree.queryCount (fun p => decide (p.1 = i)) x

theorem sum_blockCost (tree : DecisionTree (I × T) Output) (x : I × T → Bool) :
    (∑ i, tree.blockCost i x) = tree.queryCost x := by
  induction tree with
  | leaf answer => simp [blockCost, queryCount, queryCost]
  | node p zero one ihz iho =>
    simp only [blockCost] at ihz iho
    simp only [blockCost, queryCount, queryCost]
    rw [Finset.sum_add_distrib]
    have hc : (∑ i : I, if decide (p.1 = i) then 1 else 0) = 1 := by simp
    rw [hc]
    by_cases hx : x p = true
    · simp only [hx, if_true]
      exact congrArg (fun n => 1 + n) iho
    · simp only [hx]
      exact congrArg (fun n => 1 + n) ihz

def blockSubstitution (i : I) (other : I × T → Bool) : BitSubstitution T (I × T) :=
  fun p => if p.1 = i then .inr (p.2, id) else .inl (other p)

def replaceBlock (i : I) (other : I × T → Bool) (a : T → Bool) : I × T → Bool :=
  fun p => if p.1 = i then a p.2 else other p

omit [Fintype I] in
@[simp] theorem blockSubstitution_eval (i : I) (other : I × T → Bool) (a : T → Bool) :
    (blockSubstitution i other).eval a = replaceBlock i other a := by
  funext p
  by_cases hp : p.1 = i <;> simp [blockSubstitution, BitSubstitution.eval, replaceBlock, hp]

def projectBlock (tree : DecisionTree (I × T) Output) (i : I) (other : I × T → Bool) :
    DecisionTree T Output := tree.substitute (blockSubstitution i other)

omit [Fintype I] in
@[simp] theorem eval_projectBlock (tree : DecisionTree (I × T) Output)
    (i : I) (other : I × T → Bool) (a : T → Bool) :
    (tree.projectBlock i other).eval a = tree.eval (replaceBlock i other a) := by
  simp [projectBlock]

omit [Fintype I] in
@[simp] theorem cost_projectBlock (tree : DecisionTree (I × T) Output)
    (i : I) (other : I × T → Bool) (a : T → Bool) :
    (tree.projectBlock i other).queryCost a = tree.blockCost i (replaceBlock i other a) := by
  rw [projectBlock, queryCost_substitute, blockSubstitution_eval]
  unfold blockCost
  congr 1
  funext p
  by_cases hp : p.1 = i <;> simp [blockSubstitution, hp]

omit [Fintype I] in
@[simp] theorem replaceBlock_self (i : I) (x : I × T → Bool) :
    replaceBlock i x (fun j => x (i, j)) = x := by
  funext p
  rcases p with ⟨j, t⟩
  by_cases h : j = i
  · subst j
    simp [replaceBlock]
  · simp [replaceBlock, h]

theorem sum_projectBlock_cost (tree : DecisionTree (I × T) Output) (x : I × T → Bool) :
    (∑ i, (tree.projectBlock i x).queryCost (fun j => x (i, j))) ≤ tree.depth := by
  simp only [cost_projectBlock, replaceBlock_self]
  rw [sum_blockCost]
  exact queryCost_le_depth tree x

end Blocks

end QueryComplexity.DecisionTree
