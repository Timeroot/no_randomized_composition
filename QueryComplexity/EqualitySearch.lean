import QueryComplexity.OracleTrees
import QueryComplexity.FiniteProbability

namespace QueryComplexity.EqualitySearch

open scoped BigOperators

variable {A Output : Type*} [DecidableEq A]

def hit : OracleTree A Bool Output → A → Bool
  | .leaf _, _ => false
  | .query a next, x => if x = a then true else hit (next false) x

def cost : OracleTree A Bool Output → A → ℕ
  | .leaf _, _ => 0
  | .query a next, x => 1 + cost (next (decide (x = a))) x

def hits (tree : OracleTree A Bool Output) (S : Finset A) : Finset A :=
  S.filter (fun x => hit tree x = true)

theorem hits_card_le (tree : OracleTree A Bool Output) (S : Finset A) :
    (hits tree S).card ≤ S.card := Finset.card_filter_le _ _

/-- Finding a uniformly placed marked item costs at least half the number
of candidates, averaged over the runs which find it. The algorithm may
stop early, repeat queries, and do arbitrary extra work after a hit. -/
theorem single_search_bound (tree : OracleTree A Bool Output) (S : Finset A) :
    S.card * (hits tree S).card ≤ 2 * ∑ x ∈ S, cost tree x := by
  induction tree generalizing S with
  | leaf output => simp [hits, hit, cost]
  | query a next ih =>
    by_cases ha : a ∈ S
    · have hhits : hits (.query a next) S = insert a (hits (next false) (S.erase a)) := by
        ext x
        by_cases hx : x = a <;> simp [hits, hit, hx, ha]
      have ha' : a ∉ hits (next false) (S.erase a) := by simp [hits]
      have hcost : S.card + ∑ x ∈ S.erase a, cost (next false) x ≤
          ∑ x ∈ S, cost (.query a next) x := by
        simp only [cost, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
        apply Nat.add_le_add_left
        calc
          (∑ x ∈ S.erase a, cost (next false) x) =
              ∑ x ∈ S.erase a, cost (next (decide (x = a))) x := by
                apply Finset.sum_congr rfl
                intro x hx
                simp [(Finset.mem_erase.mp hx).1]
          _ ≤ ∑ x ∈ S, cost (next (decide (x = a))) x :=
            Finset.sum_le_sum_of_subset (Finset.erase_subset a S)
      have hi := ih false (S.erase a)
      have hc := hits_card_le (next false) (S.erase a)
      have hs := Finset.card_erase_add_one ha
      rw [hhits, Finset.card_insert_of_notMem ha']
      nlinarith
    · have hhits : hits (.query a next) S = hits (next false) S := by
        ext x
        by_cases hx : x = a <;> simp [hits, hit, hx, ha]
      have hcost : (∑ x ∈ S, cost (next false) x) ≤ ∑ x ∈ S, cost (.query a next) x := by
        apply Finset.sum_le_sum
        intro x hx
        have hxa : x ≠ a := by intro h; exact ha (h ▸ hx)
        simp [cost, hxa]
      rw [hhits]
      exact (ih false S).trans (Nat.mul_le_mul_left 2 hcost)

variable {I : Type*} [DecidableEq I]

def read (x : I → A) (coordinate : I × A) : Bool := decide (x coordinate.1 = coordinate.2)

def costAt : OracleTree (I × A) Bool Output → (I → A) → I → ℕ
  | .leaf _, _, _ => 0
  | .query coordinate next, x, i =>
    (if coordinate.1 = i then 1 else 0) + costAt (next (read x coordinate)) x i

def hitAt : OracleTree (I × A) Bool Output → (I → A) → I → Bool
  | .leaf _, _, _ => false
  | .query coordinate next, x, i =>
    if coordinate.1 = i ∧ x i = coordinate.2 then true
    else hitAt (next (read x coordinate)) x i

def focus : OracleTree (I × A) Bool Output →
    (i : I) → ({j : I // j ≠ i} → A) → OracleTree A Bool Output
  | .leaf output, _, _ => .leaf output
  | .query coordinate next, i, rest =>
    if hi : coordinate.1 = i then
      .query coordinate.2 (fun b => focus (next b) i rest)
    else focus (next (decide (rest ⟨coordinate.1, hi⟩ = coordinate.2))) i rest

theorem focus_cost (tree : OracleTree (I × A) Bool Output) (i : I)
    (rest : {j : I // j ≠ i} → A) (a : A) :
    cost (focus tree i rest) a =
      costAt tree ((Equiv.funSplitAt i A).symm (a, rest)) i := by
  induction tree with
  | leaf output => rfl
  | query coordinate next ih =>
    by_cases hi : coordinate.1 = i
    · simp [focus, hi, cost, costAt, read, Equiv.funSplitAt, Equiv.piSplitAt, ih]
    · simp [focus, hi, costAt, read, Equiv.funSplitAt, Equiv.piSplitAt, ih]

theorem focus_hit (tree : OracleTree (I × A) Bool Output) (i : I)
    (rest : {j : I // j ≠ i} → A) (a : A) :
    hit (focus tree i rest) a =
      hitAt tree ((Equiv.funSplitAt i A).symm (a, rest)) i := by
  induction tree with
  | leaf output => rfl
  | query coordinate next ih =>
    by_cases hi : coordinate.1 = i
    · by_cases ha : a = coordinate.2 <;>
        simp [focus, hi, hit, hitAt, read, Equiv.funSplitAt, Equiv.piSplitAt, ha, ih]
    · simp [focus, hi, hitAt, read, Equiv.funSplitAt, Equiv.piSplitAt, ih]

variable [Fintype I] [Fintype A]

theorem coordinate_search_bound (tree : OracleTree (I × A) Bool Output) (i : I) :
    Fintype.card A * (∑ x : I → A, if hitAt tree x i then 1 else 0) ≤
      2 * ∑ x : I → A, costAt tree x i := by
  have hsplit (f : (I → A) → ℕ) : ∑ x, f x =
      ∑ rest : {j : I // j ≠ i} → A, ∑ a : A,
        f ((Equiv.funSplitAt i A).symm (a, rest)) := by
    calc
      _ = ∑ p : A × ({j : I // j ≠ i} → A),
          f ((Equiv.funSplitAt i A).symm p) :=
        (Equiv.sum_comp (Equiv.funSplitAt i A).symm f).symm
      _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [hsplit, hsplit, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro rest _
  have h := single_search_bound (focus tree i rest) Finset.univ
  simpa only [Finset.card_univ, hits, Finset.card_filter, focus_hit, focus_cost] using h

theorem total_cost_le_depth (tree : OracleTree (I × A) Bool Output) (x : I → A) :
    (∑ i, costAt tree x i) ≤ tree.depth := by
  induction tree with
  | leaf output => simp [costAt, OracleTree.depth]
  | query coordinate next ih =>
    have hb : (next (read x coordinate)).depth ≤ Finset.univ.sup (fun b => (next b).depth) :=
      Finset.le_sup (f := fun b : Bool => (next b).depth) (Finset.mem_univ _)
    simp only [costAt, Finset.sum_add_distrib, OracleTree.depth]
    have hs : (∑ i : I, if coordinate.1 = i then 1 else 0) = 1 := by simp
    rw [hs]
    have hi := ih (read x coordinate)
    omega

def discoveries (tree : OracleTree (I × A) Bool Output) (x : I → A) : ℕ :=
  ∑ i, if hitAt tree x i then 1 else 0

theorem total_search_bound (tree : OracleTree (I × A) Bool Output) :
    Fintype.card A * (∑ x : I → A, discoveries tree x) ≤
      2 * Fintype.card (I → A) * tree.depth := by
  calc
    _ = ∑ i, Fintype.card A * (∑ x : I → A, if hitAt tree x i then 1 else 0) := by
      simp only [discoveries, Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ ∑ i, 2 * ∑ x : I → A, costAt tree x i :=
      Finset.sum_le_sum (fun i _ => coordinate_search_bound tree i)
    _ = 2 * ∑ x : I → A, ∑ i, costAt tree x i := by
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ 2 * ∑ x : I → A, tree.depth :=
      Nat.mul_le_mul_left 2 (Finset.sum_le_sum (fun x _ => total_cost_le_depth tree x))
    _ = _ := by simp [mul_assoc]

theorem expected_discoveries_bound (tree : OracleTree (I × A) Bool Output)
    (hA : 0 < Fintype.card A) (hX : 0 < Fintype.card (I → A)) :
    (∑ x : I → A, FiniteProbability.uniformWeight (I → A) x * (discoveries tree x : ℝ)) ≤
      2 * tree.depth / Fintype.card A := by
  have h := total_search_bound tree
  have hr : (Fintype.card A : ℝ) * (∑ x : I → A, (discoveries tree x : ℝ)) ≤
      2 * Fintype.card (I → A) * tree.depth := by exact_mod_cast h
  simp only [FiniteProbability.uniformWeight, ← Finset.mul_sum]
  apply (le_div_iff₀ (by exact_mod_cast hA)).2
  have hX' : (0 : ℝ) < Fintype.card (I → A) := by exact_mod_cast hX
  have hd := (div_le_div_iff_of_pos_right hX').2 hr
  convert hd using 1 <;> field_simp <;> ring

end QueryComplexity.EqualitySearch
