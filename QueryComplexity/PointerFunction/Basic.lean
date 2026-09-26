import QueryComplexity.Basic
import Mathlib.Tactic

/-! The total pointer predicate from the construction. The cell decoder is
an explicit parameter here; a later encoding lemma must supply the required
linear decoder and its privacy properties. No such properties are assumed
in the definitions or uniqueness proofs below. -/

namespace QueryComplexity

structure PointerCell (q : ℕ) where
  bit : Bool
  row : Fin q → Option (Fin q)
  col : Option (Fin q)
  deriving DecidableEq, Fintype

abbrev PointerInput (q : ℕ) := Fin q → Fin q → PointerCell q

namespace Pointer

def allOne {q : ℕ} (x : PointerInput q) (j : Fin q) : Prop :=
  ∀ i, (x i j).bit = true

def good {q : ℕ} (x : PointerInput q) (i j r c : Fin q) : Prop :=
  (x r c).col = some j ∧ (x r c).row j = some i

/-- A special cell and its linked rows certify the complete pointer predicate.
All unmentioned fields remain unrestricted. -/
def Valid {q : ℕ} (x : PointerInput q) (i j : Fin q) (linked : Fin q → Fin q) : Prop := by
  classical
  exact allOne x j ∧
  (∀ r, r ≠ i → ∀ c, c ≠ j → (x r j).row c = none) ∧
  (∀ c, c ≠ j → (x i j).row c = some (linked c) ∧
    (x (linked c) c).bit = false) ∧
  (Finset.univ.filter (fun c => c ≠ j ∧ good x i j (linked c) c)).card = (q - 1) / 2

noncomputable def value {q : ℕ} (x : PointerInput q) : Bool := by
  classical
  exact decide (∃ i j linked, Valid x i j linked)

@[simp] theorem value_eq_true_iff {q : ℕ} (x : PointerInput q) :
    value x = true ↔ ∃ i j linked, Valid x i j linked := by
  classical
  simp [value]

theorem valid_unique_column {q : ℕ} {x : PointerInput q}
    {i j i' j' : Fin q} {linked linked' : Fin q → Fin q}
    (h : Valid x i j linked) (h' : Valid x i' j' linked') : j = j' := by
  by_contra hne
  have hz := (h.2.2.1 j' (Ne.symm hne)).2
  have ho := h'.1 (linked j')
  rw [hz] at ho
  cases ho

theorem valid_unique_cell {q : ℕ} (hq : 2 ≤ q) {x : PointerInput q}
    {i j i' j' : Fin q} {linked linked' : Fin q → Fin q}
    (h : Valid x i j linked) (h' : Valid x i' j' linked') : i = i' ∧ j = j' := by
  have hj := valid_unique_column h h'
  subst j'
  refine ⟨?_, rfl⟩
  by_contra hne
  have hex : ∃ c : Fin q, c ≠ j := by
    by_cases hj0 : j = ⟨0, by omega⟩
    · refine ⟨⟨1, by omega⟩, ?_⟩
      rw [hj0]
      simp
    · exact ⟨⟨0, by omega⟩, Ne.symm hj0⟩
  obtain ⟨c, hc⟩ := hex
  have hn := h.2.1 i' (Ne.symm hne) c hc
  have hs := (h'.2.2.1 c hc).1
  rw [hn] at hs
  cases hs

/-- Encode each cell independently by a total Boolean map. -/
def decodeInput {q : ℕ} {C : Type*} (decode : (C → Bool) → PointerCell q)
    (x : (Fin q × Fin q) × C → Bool) : PointerInput q :=
  fun i j => decode (fun c => x ((i, j), c))

noncomputable def encoded {q : ℕ} {C : Type*}
    (decode : (C → Bool) → PointerCell q) : BoolFn ((Fin q × Fin q) × C) :=
  fun x => value (decodeInput decode x)

/-- Odd majority. The definition is total also when the arity is even. -/
def majority (q : ℕ) : BoolFn (Fin q) :=
  fun x => decide (q < 2 * (Finset.univ.filter (fun i => x i = true)).card)

/-- The total inner function, before reindexing its finite coordinate type. -/
noncomputable def inner {q : ℕ} {C : Type*}
    (decode : (C → Bool) → PointerCell q) : BoolFn (Fin q × ((Fin q × Fin q) × C)) :=
  comp (majority q) (encoded decode)


end Pointer
end QueryComplexity

namespace QueryComplexity.Pointer

def canonicalLinks {q : ℕ} (x : PointerInput q) (i j : Fin q) : Fin q → Fin q :=
  fun c => ((x i j).row c).getD i

theorem canonicalLinks_eq {q : ℕ} {x : PointerInput q} {i j : Fin q}
    {linked : Fin q → Fin q} (h : Valid x i j linked) (c : Fin q) (hc : c ≠ j) :
    canonicalLinks x i j c = linked c := by
  simp [canonicalLinks, (h.2.2.1 c hc).1]

theorem valid_change_links {q : ℕ} {x : PointerInput q} {i j : Fin q}
    {linked linked' : Fin q → Fin q} (h : Valid x i j linked)
    (heq : ∀ c, c ≠ j → linked' c = linked c) : Valid x i j linked' := by
  classical
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · intro c hc
    rw [heq c hc]
    exact h.2.2.1 c hc
  · have hf : Finset.univ.filter (fun c => c ≠ j ∧ good x i j (linked' c) c) =
        Finset.univ.filter (fun c => c ≠ j ∧ good x i j (linked c) c) := by
      ext c
      by_cases hc : c = j
      · simp [hc]
      · simp [hc, heq c hc]
    rw [hf]
    exact h.2.2.2

theorem exists_valid_iff_canonical {q : ℕ} (x : PointerInput q) (i j : Fin q) :
    (∃ linked, Valid x i j linked) ↔ Valid x i j (canonicalLinks x i j) := by
  constructor
  · rintro ⟨linked, h⟩
    exact valid_change_links h (canonicalLinks_eq h)
  · exact fun h => ⟨_, h⟩

/-- Verifying a fixed candidate requires only its column and linked cells. -/
theorem valid_of_agree {q : ℕ} {x y : PointerInput q} {i j : Fin q}
    {linked : Fin q → Fin q} (h : Valid x i j linked)
    (hcolumn : ∀ r, x r j = y r j)
    (hlinked : ∀ c, c ≠ j → x (linked c) c = y (linked c) c) :
    Valid y i j linked := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r
    rw [← hcolumn r]
    exact h.1 r
  · intro r hr c hc
    rw [← hcolumn r]
    exact h.2.1 r hr c hc
  · intro c hc
    rw [← hcolumn i, ← hlinked c hc]
    exact h.2.2.1 c hc
  · have hf : Finset.univ.filter (fun c => c ≠ j ∧ good y i j (linked c) c) =
        Finset.univ.filter (fun c => c ≠ j ∧ good x i j (linked c) c) := by
      ext c
      by_cases hc : c = j
      · simp [hc]
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, good]
        rw [← hlinked c hc]
    rw [hf]
    exact h.2.2.2

theorem valid_iff_of_agree {q : ℕ} {x y : PointerInput q} {i j : Fin q}
    {linked : Fin q → Fin q}
    (hcolumn : ∀ r, x r j = y r j)
    (hlinked : ∀ c, c ≠ j → x (linked c) c = y (linked c) c) :
    Valid x i j linked ↔ Valid y i j linked :=
  ⟨fun h => valid_of_agree h hcolumn hlinked,
    fun h => valid_of_agree h (fun r => (hcolumn r).symm) (fun c hc => (hlinked c hc).symm)⟩

end QueryComplexity.Pointer

/-! A finite alphabet encoding for pointer cells. -/

namespace QueryComplexity

def pointerCellEquiv (q : ℕ) :
    PointerCell q ≃ Bool × (Fin q → Option (Fin q)) × Option (Fin q) where
  toFun c := (c.bit, c.row, c.col)
  invFun c := ⟨c.1, c.2.1, c.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance pointerCellNonempty (q : ℕ) : Nonempty (PointerCell q) :=
  ⟨⟨false, fun _ => none, none⟩⟩

theorem pointerCell_card_bound (q : ℕ) :
    Fintype.card (PointerCell q) ≤ 2 ^ (1 + q * (q + 1)) := by
  rw [Fintype.card_congr (pointerCellEquiv q)]
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fun,
    Fintype.card_option, Fintype.card_fin]
  have hq : q + 1 ≤ 2 ^ q := Nat.succ_le_of_lt Nat.lt_two_pow_self
  calc
    2 * ((q + 1) ^ q * (q + 1)) ≤ 2 * ((2 ^ q) ^ q * 2 ^ q) := by gcongr
    _ = 2 ^ (1 + q * (q + 1)) := by
      rw [pow_add, pow_mul, pow_one, pow_succ]

end QueryComplexity
