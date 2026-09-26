import QueryComplexity.EqualitySearch
import QueryComplexity.PointerCellTrees
import QueryComplexity.PointerLayers
import QueryComplexity.PointerVariance

namespace QueryComplexity.PointerDistributions

open scoped BigOperators

attribute [local instance] Classical.propDecidable

abbrev BlockCellTree (q : ℕ) (Output : Type*) :=
  OracleTree (Fin q × (Fin q × Fin q)) (PointerCell q) Output

def fixedLabelInput {q : ℕ} (z : Fin q → Bool) (positiveInputs : BlockInput q)
    (hidden : (Fin q × Fin q) → Fin q) : BlockInput q :=
  fun i => if z i then positiveInputs i else negative (fun col => hidden (i, col))

def blockRead {q : ℕ} (x : BlockInput q) (coordinate : Fin q × (Fin q × Fin q)) :
    PointerCell q := x coordinate.1 coordinate.2.1 coordinate.2.2

/-- Fixing the positive blocks leaves ordinary equality searches for the
independent hidden rows in all negative blocks. -/
def searchTree {q : ℕ} {Output : Type*} : BlockCellTree q Output →
    (Fin q → Bool) → BlockInput q → OracleTree ((Fin q × Fin q) × Fin q) Bool Output
  | .leaf output, _, _ => .leaf output
  | .query coordinate next, z, positiveInputs =>
    if z coordinate.1 then
      searchTree (next (blockRead positiveInputs coordinate)) z positiveInputs
    else .query ((coordinate.1, coordinate.2.2), coordinate.2.1)
      (fun found => searchTree (next (blankCell q (!found))) z positiveInputs)

theorem searchTree_depth_le {q : ℕ} {Output : Type*} (tree : BlockCellTree q Output)
    (z : Fin q → Bool) (positiveInputs : BlockInput q) :
    (searchTree tree z positiveInputs).depth ≤ tree.depth := by
  induction tree with
  | leaf output => rfl
  | query coordinate next ih =>
    have hb (answer : PointerCell q) :
        (next answer).depth ≤ Finset.univ.sup (fun a => (next a).depth) :=
      Finset.le_sup (f := fun a : PointerCell q => (next a).depth) (Finset.mem_univ _)
    cases hz : z coordinate.1
    · simp only [searchTree, hz, Bool.false_eq_true, ↓reduceIte, OracleTree.depth]
      apply Nat.add_le_add_left
      apply Finset.sup_le
      intro b _
      exact (ih (blankCell q (!b))).trans (hb _)
    · simp only [searchTree, hz, ↓reduceIte, OracleTree.depth]
      have := (ih (blockRead positiveInputs coordinate)).trans (hb _)
      omega

theorem negative_read {q : ℕ} (z : Fin q → Bool) (positiveInputs : BlockInput q)
    (hidden : (Fin q × Fin q) → Fin q) (coordinate : Fin q × (Fin q × Fin q))
    (hz : z coordinate.1 = false) :
    blockRead (fixedLabelInput z positiveInputs hidden) coordinate =
      blankCell q (!(EqualitySearch.read hidden ((coordinate.1, coordinate.2.2), coordinate.2.1))) := by
  simp only [blockRead, fixedLabelInput, hz, Bool.false_eq_true, ↓reduceIte, negative,
    EqualitySearch.read]
  congr 1
  by_cases heq : coordinate.2.1 = hidden (coordinate.1, coordinate.2.2)
  · simp only [heq, ne_eq, not_true_eq_false, decide_false, decide_true, Bool.not_true,
      eq_self_iff_true]
  · simp [heq, Ne.symm heq]

theorem searchTree_hit_iff {q : ℕ} {Output : Type*} (tree : BlockCellTree q Output)
    (z : Fin q → Bool) (positiveInputs : BlockInput q) (hidden : (Fin q × Fin q) → Fin q)
    (i col : Fin q) :
    EqualitySearch.hitAt (searchTree tree z positiveInputs) hidden (i, col) = true ↔
      z i = false ∧ (i, (hidden (i, col), col)) ∈
        tree.queried (tree.route (blockRead (fixedLabelInput z positiveInputs hidden))) := by
  induction tree with
  | leaf output => simp [searchTree, EqualitySearch.hitAt, OracleTree.queried, OracleTree.transcript]
  | query coordinate next ih =>
    cases hz : z coordinate.1
    · simp only [searchTree, hz, Bool.false_eq_true, ↓reduceIte, EqualitySearch.hitAt,
        OracleTree.queried, OracleTree.route, OracleTree.transcript,
        List.map_cons, List.toFinset_cons, Finset.mem_insert]
      rw [negative_read z positiveInputs hidden coordinate hz]
      have hi := ih (blankCell q (!(EqualitySearch.read hidden
        ((coordinate.1, coordinate.2.2), coordinate.2.1))))
      simp only [OracleTree.queried] at hi
      by_cases hcoord : (coordinate.1, coordinate.2.2) = (i, col)
      · have hi' : coordinate.1 = i := congrArg Prod.fst hcoord
        have hc' : coordinate.2.2 = col := congrArg Prod.snd hcoord
        have hzi : z i = false := hi' ▸ hz
        by_cases hr : hidden (i, col) = coordinate.2.1
        · simp [hcoord, hzi, ← hi', ← hc', hr, hz]
        · have hne : (i, (hidden (i, col), col)) ≠ coordinate := by
            intro heq
            exact hr (congrArg (fun c => c.2.1) heq)
          simp only [hcoord] at hi
          simp only [hcoord, hr, and_false, ↓reduceIte, hi, hne, false_or]
      · have hne : (i, (hidden (i, col), col)) ≠ coordinate := by
          intro heq
          apply hcoord
          exact Prod.ext (congrArg (fun c => c.1) heq).symm
            (congrArg (fun c => c.2.2) heq).symm
        simp [hcoord, hi, hne]
    · have hread : blockRead (fixedLabelInput z positiveInputs hidden) coordinate =
          blockRead positiveInputs coordinate := by simp [blockRead, fixedLabelInput, hz]
      simp only [searchTree, hz, ↓reduceIte, OracleTree.queried, OracleTree.route,
        OracleTree.transcript, List.map_cons, List.toFinset_cons, Finset.mem_insert]
      rw [hread]
      have hi := ih (blockRead positiveInputs coordinate)
      simp only [OracleTree.queried] at hi
      rw [hi]
      constructor
      · rintro ⟨hzi, hmem⟩; exact ⟨hzi, Or.inr hmem⟩
      · rintro ⟨hzi, heq | hmem⟩
        · have hi' := congrArg (fun c => c.1) heq
          have hieq : i = coordinate.1 := hi'
          have : z i = true := by rw [hieq]; exact hz
          simp_all
        · exact ⟨hzi, hmem⟩

def trackedDiscoveries {q : ℕ} {Output : Type*} (tree : BlockCellTree q Output)
    (z : Fin q → Bool) (positiveInputs : BlockInput q) (hidden : (Fin q × Fin q) → Fin q) : ℕ :=
  (Finset.univ.filter (fun p : Fin q × Fin q => z p.1 = false ∧
    (p.1, (hidden p, p.2)) ∈ tree.queried
      (tree.route (blockRead (fixedLabelInput z positiveInputs hidden))))).card

theorem trackedDiscoveries_eq {q : ℕ} {Output : Type*} (tree : BlockCellTree q Output)
    (z : Fin q → Bool) (positiveInputs : BlockInput q) (hidden : (Fin q × Fin q) → Fin q) :
    trackedDiscoveries tree z positiveInputs hidden =
      EqualitySearch.discoveries (searchTree tree z positiveInputs) hidden := by
  unfold trackedDiscoveries EqualitySearch.discoveries
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro p _
  simp only [← searchTree_hit_iff tree z positiveInputs hidden p.1 p.2]

theorem expected_trackedDiscoveries_bound {q : ℕ} {Output : Type*} (hq : 0 < q)
    (tree : BlockCellTree q Output) (z : Fin q → Bool) (positiveInputs : BlockInput q) :
    (∑ hidden : (Fin q × Fin q) → Fin q,
      FiniteProbability.uniformWeight ((Fin q × Fin q) → Fin q) hidden *
        (trackedDiscoveries tree z positiveInputs hidden : ℝ)) ≤ 2 * tree.depth / q := by
  letI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  simp_rw [trackedDiscoveries_eq]
  have h := EqualitySearch.expected_discoveries_bound (searchTree tree z positiveInputs)
    (by simpa using hq) Fintype.card_pos
  apply h.trans
  simp only [Fintype.card_fin]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg q)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast searchTree_depth_le tree z positiveInputs)
    (by norm_num)

theorem localQueried_mem_iff {q : ℕ} {Output : Type*} (tree : BlockCellTree q Output)
    (leaf : tree.Leaf) (i : Fin q) (coordinate : Fin q × Fin q) :
    coordinate ∈ localQueried (tree.transcript leaf) i ↔ (i, coordinate) ∈ tree.queried leaf := by
  classical
  simp only [localQueried, Finset.mem_filter, Finset.mem_univ, true_and, OracleTree.queried,
    List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨answer, ha⟩
    exact ⟨((i, coordinate), answer), ha, rfl⟩
  · rintro ⟨⟨coord, answer⟩, ha, heq⟩
    dsimp only at heq
    subst coord
    exact ⟨answer, ha⟩

theorem trackedDiscoveries_sum {q : ℕ} {Output : Type*} (tree : BlockCellTree q Output)
    (z : Fin q → Bool) (positiveInputs : BlockInput q) (hidden : (Fin q × Fin q) → Fin q) :
    trackedDiscoveries tree z positiveInputs hidden =
      ∑ i ∈ Finset.univ.filter (fun i => z i = false),
        (discovered (localQueried (tree.transcript
          (tree.route (blockRead (fixedLabelInput z positiveInputs hidden)))) i)
          (fun col => hidden (i, col))).card := by
  classical
  simp only [trackedDiscoveries, Finset.card_filter, Fintype.sum_prod_type,
    Finset.sum_filter, discovered, localQueried_mem_iff]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hz : z i = false <;> simp [hz]

theorem fixedLabel_negative_compatible {q : ℕ} {Output : Type*} (tree : BlockCellTree q Output)
    (z : Fin q → Bool) (positiveInputs : BlockInput q) (hidden : (Fin q × Fin q) → Fin q)
    (i : Fin q) (hi : z i = false) :
    OraclePosteriors.localMatches cellInput (tree.transcript
      (tree.route (blockRead (fixedLabelInput z positiveInputs hidden)))) i
        (negative (fun col => hidden (i, col))) := by
  have h := (OraclePosteriors.matches_iff_local cellInput
    (tree.transcript (tree.route (blockRead (fixedLabelInput z positiveInputs hidden))))
    (fixedLabelInput z positiveInputs hidden)).1
      (tree.route_matches (blockRead (fixedLabelInput z positiveInputs hidden))) i
  simpa [fixedLabelInput, hi] using h

theorem fixedLabel_variance_lower {q r : ℕ} {Output : Type*} (hq : 5 ≤ q) (hr : 0 < r)
    (hrsmall : 4 * r ≤ q) (tree : BlockCellTree q Output) (z : Fin q → Bool)
    (hnegative : q ≤ 2 * (Finset.univ.filter (fun i => z i = false)).card + 1)
    (positiveInputs : BlockInput q) (hidden : (Fin q × Fin q) → Fin q)
    (hbudget : 8 * trackedDiscoveries tree z positiveInputs hidden ≤ q * r) :
    (q : ℝ) / (16 * (5 : ℝ) ^ r) ≤ PosteriorMajority.variance
      (localPosterior (tree.transcript (tree.route
        (blockRead (fixedLabelInput z positiveInputs hidden))))) := by
  apply localPosterior_variance_sum_lower hq hr hrsmall _
    (Finset.univ.filter (fun i => z i = false)) (fun i col => hidden (i, col))
  · intro i hi
    exact fixedLabel_negative_compatible tree z positiveInputs hidden i (Finset.mem_filter.mp hi).2
  · exact hnegative
  · rwa [← trackedDiscoveries_sum]

noncomputable def varianceGood {q : ℕ} {Output : Type*} (tree : BlockCellTree q Output)
    (v : ℝ) (x : BlockInput q) : Prop :=
  v ≤ PosteriorMajority.variance (localPosterior (tree.transcript (tree.route (blockRead x))))

theorem fixedLabel_bad_variance_bound {q r : ℕ} {Output : Type*} (hq : 5 ≤ q) (hr : 0 < r)
    (hrsmall : 4 * r ≤ q) (tree : BlockCellTree q Output) (z : Fin q → Bool)
    (hnegative : q ≤ 2 * (Finset.univ.filter (fun i => z i = false)).card + 1)
    (positiveInputs : BlockInput q) :
    (∑ hidden : (Fin q × Fin q) → Fin q,
      FiniteProbability.uniformWeight ((Fin q × Fin q) → Fin q) hidden *
        (if varianceGood tree ((q : ℝ) / (16 * (5 : ℝ) ^ r))
          (fixedLabelInput z positiveInputs hidden) then (0 : ℝ) else 1)) ≤
      (2 * tree.depth / q) / ((q : ℝ) * r / 8) := by
  classical
  have hden : (0 : ℝ) < (q : ℝ) * r / 8 := by positivity
  calc
    _ ≤ ∑ hidden : (Fin q × Fin q) → Fin q,
      FiniteProbability.uniformWeight ((Fin q × Fin q) → Fin q) hidden *
        ((trackedDiscoveries tree z positiveInputs hidden : ℝ) / ((q : ℝ) * r / 8)) := by
      apply Finset.sum_le_sum
      intro hidden _
      apply mul_le_mul_of_nonneg_left _ (FiniteProbability.uniformWeight_nonnegative _ hidden)
      split_ifs with hgood
      · positivity
      · have hfail : q * r < 8 * trackedDiscoveries tree z positiveInputs hidden := by
          by_contra h
          exact hgood (fixedLabel_variance_lower hq hr hrsmall tree z hnegative positiveInputs hidden
            (by omega))
        apply (one_le_div hden).2
        have hreal : (q : ℝ) * r < 8 * (trackedDiscoveries tree z positiveInputs hidden : ℝ) := by
          exact_mod_cast hfail
        linarith
    _ = (∑ hidden : (Fin q × Fin q) → Fin q,
      FiniteProbability.uniformWeight ((Fin q × Fin q) → Fin q) hidden *
        (trackedDiscoveries tree z positiveInputs hidden : ℝ)) / ((q : ℝ) * r / 8) := by
      simp only [mul_div_assoc, Finset.sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right (expected_trackedDiscoveries_bound (by omega) tree z positiveInputs)
      hden.le

end QueryComplexity.PointerDistributions
