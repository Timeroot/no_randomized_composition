import QueryComplexity.PointerObservations
import QueryComplexity.FiniteCartesian

namespace QueryComplexity.PointerDistributions

def queriedRows {q : ℕ} (queried : Finset (Fin q × Fin q)) (col : Fin q) : Finset (Fin q) :=
  Finset.univ.filter (fun row => (row, col) ∈ queried)

def allowedRows {q : ℕ} (queried : Finset (Fin q × Fin q))
    (reference : Fin q → Fin q) (col : Fin q) : Finset (Fin q) :=
  if reference col ∈ queriedRows queried col then {reference col} else (queriedRows queried col)ᶜ

theorem reference_mem_allowedRows {q : ℕ} (queried : Finset (Fin q × Fin q))
    (reference : Fin q → Fin q) (col : Fin q) :
    reference col ∈ allowedRows queried reference col := by
  by_cases h : reference col ∈ queriedRows queried col <;> simp [allowedRows, h]

theorem observes_negative_iff_allowed {q : ℕ} (queried : Finset (Fin q × Fin q))
    (hidden reference : Fin q → Fin q) :
    Observes queried (negative hidden) (negative reference) ↔
      ∀ col, hidden col ∈ allowedRows queried reference col := by
  constructor
  · intro hobs col
    by_cases href : reference col ∈ queriedRows queried col
    · have hquery : (reference col, col) ∈ queried := by simpa [queriedRows] using href
      have hrow := (observes_negative_hidden_eq queried hidden reference hobs
        (reference col) col hquery).2 rfl
      rw [allowedRows, if_pos href]
      exact Finset.mem_singleton.mpr hrow.symm
    · simp only [allowedRows, if_neg href, Finset.mem_compl]
      intro hhidden
      have hquery : (hidden col, col) ∈ queried := by simpa [queriedRows] using hhidden
      have hrow := (observes_negative_hidden_eq queried hidden reference hobs
        (hidden col) col hquery).1 rfl
      exact href (by simpa [hrow] using hhidden)
  · intro hallowed coordinate hquery
    have hquery' : coordinate.1 ∈ queriedRows queried coordinate.2 := by
      simpa [queriedRows] using hquery
    by_cases href : reference coordinate.2 ∈ queriedRows queried coordinate.2
    · have hrow : hidden coordinate.2 = reference coordinate.2 := by
        simpa [allowedRows, href] using hallowed coordinate.2
      simp [negative, hrow]
    · have hhidden : hidden coordinate.2 ∉ queriedRows queried coordinate.2 := by
        simpa [allowedRows, href] using hallowed coordinate.2
      have hrow : coordinate.1 ≠ hidden coordinate.2 := by
        intro heq; exact hhidden (heq ▸ hquery')
      have hrow' : coordinate.1 ≠ reference coordinate.2 := by
        intro heq; exact href (heq ▸ hquery')
      simp [negative, hrow, hrow']

def compatibleHiddenEquiv {q : ℕ} (queried : Finset (Fin q × Fin q))
    (reference : Fin q → Fin q) :
    {hidden : Fin q → Fin q // Observes queried (negative hidden) (negative reference)} ≃
      (∀ col, allowedRows queried reference col) where
  toFun hidden col := ⟨hidden.1 col, (observes_negative_iff_allowed queried hidden.1 reference).1 hidden.2 col⟩
  invFun hidden := ⟨fun col => (hidden col).1,
    (observes_negative_iff_allowed queried _ reference).2 (fun col => (hidden col).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def compatibleHiddenFiberEquiv {q : ℕ} (queried : Finset (Fin q × Fin q))
    (reference : Fin q → Fin q) (col : Fin q) (row : allowedRows queried reference col) :
    {hidden : Fin q → Fin q //
      Observes queried (negative hidden) (negative reference) ∧ hidden col = row.1} ≃
      {hidden : ∀ c, allowedRows queried reference c // hidden col = row} where
  toFun hidden := ⟨compatibleHiddenEquiv queried reference ⟨hidden.1, hidden.2.1⟩,
    Subtype.ext hidden.2.2⟩
  invFun hidden := ⟨fun col => (hidden.1 col).1,
    (observes_negative_iff_allowed queried _ reference).2 (fun col => (hidden.1 col).2),
    congrArg Subtype.val hidden.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Conditional on any fixed negative transcript, an undiscovered hidden
row is uniform over exactly its allowed rows. -/
theorem conditional_hidden_row_probability {q : ℕ}
    (queried : Finset (Fin q × Fin q)) (reference : Fin q → Fin q)
    (col : Fin q) (row : allowedRows queried reference col) :
    (Nat.card {hidden : Fin q → Fin q //
      Observes queried (negative hidden) (negative reference) ∧ hidden col = row.1} : ℝ) /
        (Nat.card {hidden : Fin q → Fin q //
          Observes queried (negative hidden) (negative reference)} : ℝ) =
      1 / (allowedRows queried reference col).card := by
  letI : ∀ col, Nonempty (allowedRows queried reference col) :=
    fun col => ⟨⟨reference col, reference_mem_allowedRows queried reference col⟩⟩
  rw [Nat.card_congr (compatibleHiddenFiberEquiv queried reference col row),
    Nat.card_congr (compatibleHiddenEquiv queried reference)]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    FiniteCartesian.pi_fiber_probability (fun c => allowedRows queried reference c) col row

/-- A fresh query in a column with at most half its rows queried discovers
its hidden cell with conditional probability at most `2/q`. -/
theorem early_discovery_bound {q : ℕ} (hq : 0 < q)
    (queried : Finset (Fin q × Fin q)) (reference : Fin q → Fin q)
    (col row : Fin q) (hunknown : reference col ∉ queriedRows queried col)
    (hfresh : row ∉ queriedRows queried col) (hearly : 2 * (queriedRows queried col).card ≤ q) :
    (Nat.card {hidden : Fin q → Fin q //
      Observes queried (negative hidden) (negative reference) ∧ hidden col = row} : ℝ) /
        (Nat.card {hidden : Fin q → Fin q //
          Observes queried (negative hidden) (negative reference)} : ℝ) ≤ 2 / q := by
  have hrow : row ∈ allowedRows queried reference col := by simp [allowedRows, hunknown, hfresh]
  rw [conditional_hidden_row_probability queried reference col ⟨row, hrow⟩]
  rw [allowedRows, if_neg hunknown, Finset.card_compl, Fintype.card_fin]
  have hden : 0 < q - (queriedRows queried col).card := by omega
  apply (div_le_div_iff₀ (by exact_mod_cast hden) (by exact_mod_cast hq)).2
  have hnat : q ≤ 2 * (q - (queriedRows queried col).card) := by omega
  have hreal : (q : ℝ) ≤ 2 * ((q - (queriedRows queried col).card : ℕ) : ℝ) := by
    exact_mod_cast hnat
  simpa using hreal

end QueryComplexity.PointerDistributions
