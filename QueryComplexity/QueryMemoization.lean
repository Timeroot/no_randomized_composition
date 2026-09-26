import QueryComplexity.QueryCost

/-! Caching repeated queries preserves evaluation and charges each visited
coordinate only once. -/

open scoped BigOperators

namespace QueryComplexity.DecisionTree

universe u v

variable {T : Type u} {Output : Type v} [DecidableEq T]

def visited : DecisionTree T Output → (T → Bool) → Finset T
  | .leaf _, _ => ∅
  | .node j zero one, x => insert j (if x j then visited one x else visited zero x)

def memoize (known : Finset T) (values : T → Bool) : DecisionTree T Output → DecisionTree T Output
  | .leaf answer => .leaf answer
  | .node j zero one =>
      if j ∈ known then
        if values j then memoize known values one else memoize known values zero
      else .node j
        (memoize (insert j known) (Function.update values j false) zero)
        (memoize (insert j known) (Function.update values j true) one)

theorem update_consistent (known : Finset T) (values x : T → Bool)
    (h : ∀ j ∈ known, values j = x j) (i : T) :
    ∀ j ∈ insert i known, Function.update values i (x i) j = x j := by
  intro j hj
  rcases Finset.mem_insert.mp hj with rfl | hj
  · simp
  · by_cases he : j = i
    · subst j
      simp
    · simp [he, h j hj]

theorem eval_memoize (tree : DecisionTree T Output) (known : Finset T) (values x : T → Bool)
    (h : ∀ j ∈ known, values j = x j) :
    (tree.memoize known values).eval x = tree.eval x := by
  induction tree generalizing known values with
  | leaf answer => rfl
  | node j zero one ihz iho =>
    by_cases hj : j ∈ known
    · simp only [memoize, hj, if_true, h j hj, eval]
      by_cases hx : x j = true
      · simp only [hx, if_true]
        exact iho known values h
      · have hf : x j = false := Bool.eq_false_of_not_eq_true hx
        simp only [hf, Bool.false_eq_true, if_false]
        exact ihz known values h
    · simp only [memoize, hj, if_false, eval]
      by_cases hx : x j = true
      · simp only [hx, if_true]
        apply iho
        simpa only [hx] using update_consistent known values x h j
      · have hf : x j = false := Bool.eq_false_of_not_eq_true hx
        simp only [hf, Bool.false_eq_true, if_false]
        apply ihz
        simpa only [hf] using update_consistent known values x h j

theorem card_insert_sdiff (s known : Finset T) (i : T) (hi : i ∉ known) :
    ((insert i s) \ known).card = 1 + (s \ insert i known).card := by
  have he : insert i s \ known = insert i (s \ insert i known) := by
    ext j
    by_cases hj : j = i
    · subst j
      simp [hi]
    · simp [hj]
  rw [he, Finset.card_insert_of_notMem (by simp)]
  omega

theorem queryCost_memoize (tree : DecisionTree T Output) (known : Finset T) (values x : T → Bool)
    (h : ∀ j ∈ known, values j = x j) :
    (tree.memoize known values).queryCost x = (tree.visited x \ known).card := by
  induction tree generalizing known values with
  | leaf answer => simp [memoize, queryCost, visited]
  | node j zero one ihz iho =>
    by_cases hj : j ∈ known
    · have he (s : Finset T) : insert j s \ known = s \ known := by
        ext i
        by_cases hi : i = j
        · subst i
          simp [hj]
        · simp [hi]
      simp only [memoize, hj, if_true, h j hj, visited]
      by_cases hx : x j = true
      · simp only [hx, if_true, he]
        exact iho known values h
      · have hf : x j = false := Bool.eq_false_of_not_eq_true hx
        simp only [hf, Bool.false_eq_true, if_false, he]
        exact ihz known values h
    · simp only [memoize, hj, if_false, queryCost, visited]
      by_cases hx : x j = true
      · simp only [hx, if_true]
        rw [card_insert_sdiff _ _ _ hj]
        congr 1
        apply iho
        simpa only [hx] using update_consistent known values x h j
      · have hf : x j = false := Bool.eq_false_of_not_eq_true hx
        simp only [hf, Bool.false_eq_true, if_false]
        rw [card_insert_sdiff _ _ _ hj]
        congr 1
        apply ihz
        simpa only [hf] using update_consistent known values x h j

def cached (tree : DecisionTree T Output) : DecisionTree T Output :=
  tree.memoize ∅ (fun _ => false)

@[simp] theorem eval_cached (tree : DecisionTree T Output) (x : T → Bool) :
    tree.cached.eval x = tree.eval x :=
  eval_memoize tree ∅ (fun _ => false) x (by simp)

@[simp] theorem queryCost_cached (tree : DecisionTree T Output) (x : T → Bool) :
    tree.cached.queryCost x = (tree.visited x).card := by
  simpa [cached] using queryCost_memoize tree ∅ (fun _ => false) x (by simp)

theorem mem_visited_substitute {U : Type*} [DecidableEq U]
    (σ : BitSubstitution T U) (tree : DecisionTree U Output) (x : T → Bool) (i : T) :
    i ∈ (tree.substitute σ).visited x ↔
      ∃ j ∈ tree.visited (σ.eval x), ∃ value, σ j = .inr (i, value) := by
  induction tree with
  | leaf answer => simp [substitute, visited]
  | node j zero one ihz iho =>
    cases hs : σ j with
    | inl b =>
      cases b <;> simp [substitute, visited, BitSubstitution.eval, hs, ihz, iho]
    | inr p =>
      rcases p with ⟨r, value⟩
      cases hx : x r <;> cases hv : value false <;> cases hw : value true <;>
        simp [substitute, visited, BitSubstitution.eval, hs, hx, hv, hw, ihz, iho,
          or_and_right, exists_or, eq_comm]

theorem mem_visited_projectBlock {I : Type*} [Fintype I] [DecidableEq I]
    (tree : DecisionTree (I × T) Output) (i : I) (other : I × T → Bool)
    (a : T → Bool) (j : T) :
    j ∈ (tree.projectBlock i other).visited a ↔
      (i, j) ∈ tree.visited (replaceBlock i other a) := by
  rw [projectBlock, mem_visited_substitute, blockSubstitution_eval]
  constructor
  · rintro ⟨⟨r, s⟩, hp, value, he⟩
    by_cases hr : r = i
    · subst r
      simp only [blockSubstitution, if_pos rfl] at he
      have hs : s = j := congrArg Prod.fst (Sum.inr.inj he)
      subst s
      exact hp
    · simp [blockSubstitution, hr] at he
  · intro hj
    exact ⟨(i, j), hj, id, by simp [blockSubstitution]⟩

end QueryComplexity.DecisionTree
