import QueryComplexity.PointerDistributions

/-! Exact compatibility of finite full-cell observations under the two
pointer hard-input sources. -/

namespace QueryComplexity.PointerDistributions

def Plain {q : ℕ} (cell : PointerCell q) : Prop :=
  cell.col = none ∧ ∀ j, cell.row j = none

theorem negative_plain {q : ℕ} (hidden : Fin q → Fin q) (row col : Fin q) :
    Plain (negative hidden row col) := by
  simp [Plain, negative, blankCell]

theorem exists_other_column {q : ℕ} (hq : 2 ≤ q) (special : Fin q) :
    ∃ col : Fin q, col ≠ special := by
  by_cases h : special = ⟨0, by omega⟩
  · exact ⟨⟨1, by omega⟩, by rw [h]; simp⟩
  · exact ⟨⟨0, by omega⟩, Ne.symm h⟩

theorem positive_hidden_blue_not_plain {q : ℕ} (hq : 2 ≤ q)
    (hidden : Fin q → Fin q) (blue : Finset (Fin q)) (special col : Fin q)
    (hblue : col ∈ blue) : ¬ Plain (positive hidden blue special (hidden col) col) := by
  intro hplain
  by_cases hcol : col = special
  · subst col
    obtain ⟨other, hother⟩ := exists_other_column hq special
    have := hplain.2 other
    simp [positive, hother] at this
  · have := hplain.1
    simp [positive, hcol, hblue] at this

theorem positive_eq_negative_of_safe {q : ℕ}
    (hidden : Fin q → Fin q) (blue : Finset (Fin q)) (special row col : Fin q)
    (hspecial : special ∈ blue) (hsafe : row ≠ hidden col ∨ col ∉ blue) :
    positive hidden blue special row col = negative hidden row col := by
  rcases hsafe with hrow | hblue
  · simp [positive, negative, hrow]
  · have hcol : col ≠ special := by intro h; exact hblue (h ▸ hspecial)
    by_cases hrow : row = hidden col <;> simp [positive, negative, hrow, hcol, hblue, blankCell]

def Observes {q : ℕ} (queried : Finset (Fin q × Fin q)) (x reference : PointerInput q) : Prop :=
  ∀ coordinate ∈ queried, x coordinate.1 coordinate.2 = reference coordinate.1 coordinate.2

def discovered {q : ℕ} (queried : Finset (Fin q × Fin q)) (reference : Fin q → Fin q) :
    Finset (Fin q) := Finset.univ.filter (fun col => (reference col, col) ∈ queried)

theorem observes_negative_hidden_eq {q : ℕ}
    (queried : Finset (Fin q × Fin q)) (hidden reference : Fin q → Fin q)
    (hobs : Observes queried (negative hidden) (negative reference))
    (row col : Fin q) (hquery : (row, col) ∈ queried) :
    row = hidden col ↔ row = reference col := by
  have hbits := congrArg PointerCell.bit (hobs (row, col) hquery)
  simpa [negative, blankCell] using hbits

theorem observes_positive_iff {q : ℕ} (hq : 2 ≤ q)
    (queried : Finset (Fin q × Fin q)) (hidden reference : Fin q → Fin q)
    (blue : Finset (Fin q)) (special : Fin q) (hspecial : special ∈ blue) :
    Observes queried (positive hidden blue special) (negative reference) ↔
      Observes queried (negative hidden) (negative reference) ∧
        Disjoint blue (discovered queried reference) := by
  constructor
  · intro hobs
    have hsafe : ∀ coordinate ∈ queried,
        coordinate.1 ≠ hidden coordinate.2 ∨ coordinate.2 ∉ blue := by
      intro coordinate hquery
      by_contra! hbad
      have hp : Plain (positive hidden blue special coordinate.1 coordinate.2) := by
        rw [hobs coordinate hquery]
        exact negative_plain reference coordinate.1 coordinate.2
      rw [hbad.1] at hp
      exact positive_hidden_blue_not_plain hq hidden blue special coordinate.2 hbad.2 hp
    have hnegative : Observes queried (negative hidden) (negative reference) := by
      intro coordinate hquery
      rw [← positive_eq_negative_of_safe hidden blue special coordinate.1 coordinate.2
        hspecial (hsafe coordinate hquery)]
      exact hobs coordinate hquery
    refine ⟨hnegative, ?_⟩
    apply Finset.disjoint_left.mpr
    intro col hblue hdisc
    have hquery : (reference col, col) ∈ queried := by simpa [discovered] using hdisc
    have hrow : reference col = hidden col :=
      (observes_negative_hidden_eq queried hidden reference hnegative (reference col) col hquery).2 rfl
    rcases hsafe (reference col, col) hquery with hrow' | hblue'
    · exact hrow' hrow
    · exact hblue' hblue
  · rintro ⟨hnegative, hdisjoint⟩ coordinate hquery
    have hsafe : coordinate.1 ≠ hidden coordinate.2 ∨ coordinate.2 ∉ blue := by
      by_cases hrow : coordinate.1 = hidden coordinate.2
      · right
        intro hblue
        have href : coordinate.1 = reference coordinate.2 :=
          (observes_negative_hidden_eq queried hidden reference hnegative
            coordinate.1 coordinate.2 hquery).1 hrow
        have hdisc : coordinate.2 ∈ discovered queried reference := by
          simp only [discovered, Finset.mem_filter, Finset.mem_univ, true_and]
          simpa only [← href] using hquery
        exact Finset.disjoint_left.mp hdisjoint hblue hdisc
      · exact Or.inl hrow
    rw [positive_eq_negative_of_safe hidden blue special coordinate.1 coordinate.2 hspecial hsafe]
    exact hnegative coordinate hquery

end QueryComplexity.PointerDistributions
