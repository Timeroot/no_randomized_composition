import QueryComplexity.PointerFunction.Distributions
import ForMathlib.Combinatorics.Binomial

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

namespace QueryComplexity.PointerDistributions

noncomputable def observationSampleEquiv {q : ℕ} (hq : 2 ≤ q)
    (queried : Finset (Fin q × Fin q)) (reference : Fin q → Fin q) :
    {s : PositiveSample q // Observes queried (sampledPositive s) (negative reference)} ≃
      {hidden : Fin q → Fin q // Observes queried (negative hidden) (negative reference)} ×
        {color : ColorChoice q // Disjoint color.1.1 (discovered queried reference)} where
  toFun s :=
    let h := (observes_positive_iff hq queried s.1.1 reference s.1.2.1.1 s.1.2.1.2 s.1.2.2.1).1 s.2
    (⟨s.1.1, h.1⟩, ⟨s.1.2, h.2⟩)
  invFun s := ⟨(s.1.1, s.2.1),
    (observes_positive_iff hq queried s.1.1 reference s.2.1.1.1 s.2.1.1.2 s.2.1.2.1).2
      ⟨s.1.2, s.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def negativeObservationProbability {q : ℕ}
    (queried : Finset (Fin q × Fin q)) (reference : Fin q → Fin q) : ℝ :=
  (Nat.card {hidden : Fin q → Fin q // Observes queried (negative hidden) (negative reference)} : ℝ) /
    Nat.card (Fin q → Fin q)

noncomputable def positiveObservationProbability {q : ℕ}
    (queried : Finset (Fin q × Fin q)) (reference : Fin q → Fin q) : ℝ :=
  (Nat.card {s : PositiveSample q // Observes queried (sampledPositive s) (negative reference)} : ℝ) /
    Nat.card (PositiveSample q)

theorem observation_probability_factorization {q : ℕ} (hq : 2 ≤ q)
    (queried : Finset (Fin q × Fin q)) (reference : Fin q → Fin q) :
    positiveObservationProbability queried reference =
      negativeObservationProbability queried reference *
        (((q - (discovered queried reference).card).choose ((q - 1) / 2 + 1) : ℝ) /
          (q.choose ((q - 1) / 2 + 1) : ℝ)) := by
  classical
  have hcard := Nat.card_congr (observationSampleEquiv hq queried reference)
  rw [Nat.card_prod] at hcard
  have hcolor :
      (Nat.card {color : ColorChoice q // Disjoint color.1.1 (discovered queried reference)} : ℝ) /
        Nat.card (ColorChoice q) =
      (((q - (discovered queried reference).card).choose ((q - 1) / 2 + 1) : ℝ) /
          (q.choose ((q - 1) / 2 + 1) : ℝ)) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
      PointedSetCounting.avoidance_probability (discovered queried reference) ((q - 1) / 2 + 1)
        (by omega)
  unfold positiveObservationProbability negativeObservationProbability
  rw [hcard, show Nat.card (PositiveSample q) =
      Nat.card (Fin q → Fin q) * Nat.card (ColorChoice q) from Nat.card_prod _ _]
  push_cast
  rw [← hcolor]
  simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

theorem negativeObservationProbability_pos {q : ℕ}
    (queried : Finset (Fin q × Fin q)) (reference : Fin q → Fin q) :
    0 < negativeObservationProbability queried reference := by
  classical
  letI : Nonempty (Fin q → Fin q) := ⟨reference⟩
  letI : Nonempty {hidden : Fin q → Fin q //
      Observes queried (negative hidden) (negative reference)} := ⟨⟨reference, fun _ _ => rfl⟩⟩
  apply div_pos <;> exact_mod_cast Nat.card_pos

/-- The exact likelihood ratio of any fixed transcript drawn from the
negative source depends only on the number of discovered hidden cells. -/
theorem observation_likelihood_ratio {q : ℕ} (hq : 2 ≤ q)
    (queried : Finset (Fin q × Fin q)) (reference : Fin q → Fin q) :
    positiveObservationProbability queried reference /
        negativeObservationProbability queried reference =
      (((q - (discovered queried reference).card).choose ((q - 1) / 2 + 1) : ℝ) /
          (q.choose ((q - 1) / 2 + 1) : ℝ)) := by
  rw [observation_probability_factorization hq]
  exact mul_div_cancel_left₀ _ (negativeObservationProbability_pos queried reference).ne'

theorem observation_likelihood_lower {q : ℕ} (hq : 5 ≤ q)
    (queried : Finset (Fin q × Fin q)) (reference : Fin q → Fin q)
    (hdiscover : 4 * (discovered queried reference).card ≤ q) :
    (1 : ℝ) / 5 ^ (discovered queried reference).card ≤
      positiveObservationProbability queried reference /
        negativeObservationProbability queried reference := by
  rw [observation_likelihood_ratio (by omega)]
  apply BinomialAvoidance.choose_avoid_probability_lower <;> omega

end QueryComplexity.PointerDistributions
