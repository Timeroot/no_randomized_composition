import QueryComplexity.Definitions
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

/-- The balancing identity for the detector-based weak evaluator. If the
detector accepts each positive block with probability `rho` and negatives
with probability zero, `p` is its acceptance probability after balancing. -/
theorem balanced_acceptance_identity (q rho t : ℝ) (hq : q ≠ 0) (hr : 2 - rho ≠ 0) :
    let alpha := (1 - rho) / (2 - rho)
    let p := alpha + (1 - alpha) * (rho * t / q)
    2 * p - 1 = rho * (2 * t - q) / ((2 - rho) * q) := by
  dsimp
  field_simp
  ring

theorem detector_rho_bounds (q : ℝ) (hq : 3 ≤ q) :
    (1 : ℝ) / 3 ≤ (q - 1) / (2 * q) ∧ (q - 1) / (2 * q) ≤ 1 / 2 := by
  have hq0 : 0 < q := by linarith
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 2 * q)).2
    linarith
  · apply (div_le_iff₀ (by positivity : 0 < 2 * q)).2
    linarith

/-- The exact detector probability yields the needed uniform bias scale. -/
theorem weak_bias_scale (q : ℝ) (hq : 3 ≤ q) :
    (1 : ℝ) / (5 * q) ≤
      ((q - 1) / (2 * q)) / ((2 - (q - 1) / (2 * q)) * q) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨hl, hu⟩ := detector_rho_bounds q hq
  have hd : 0 < (2 - (q - 1) / (2 * q)) * q := mul_pos (by linarith) hq0
  apply (le_div_iff₀ hd).2
  calc
    1 / (5 * q) * ((2 - (q - 1) / (2 * q)) * q) =
        (2 - (q - 1) / (2 * q)) / 5 := by field_simp
    _ ≤ (q - 1) / (2 * q) := by linarith

end Pointer
end QueryComplexity
