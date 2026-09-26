import QueryComplexity.Pointer
import QueryComplexity.Basic
import QueryComplexity.FiniteProbability

/-!
# Concrete hard pointer inputs

The negative input has one hidden zero in every column. A positive input
changes the hidden cells in a selected set of columns to a special cell and
its good back-pointers.  All other cells and fields are specified explicitly.
-/

namespace QueryComplexity.PointerDistributions

def blankCell (q : ℕ) (bit : Bool) : PointerCell q :=
  ⟨bit, fun _ => none, none⟩

def negative {q : ℕ} (hidden : Fin q → Fin q) : PointerInput q :=
  fun row col => blankCell q (decide (row ≠ hidden col))

theorem negative_value {q : ℕ} (hidden : Fin q → Fin q) :
    Pointer.value (negative hidden) = false := by
  cases h : Pointer.value (negative hidden)
  · rfl
  · obtain ⟨i, j, linked, hv⟩ := Pointer.value_eq_true_iff _ |>.mp h
    have hfalse := hv.1 (hidden j)
    simp [negative, blankCell] at hfalse

def positive {q : ℕ} (hidden : Fin q → Fin q) (blue : Finset (Fin q))
    (special : Fin q) : PointerInput q :=
  fun row col =>
    if row = hidden col then
      if col = special then
        ⟨true, fun c => if c = special then none else some (hidden c), none⟩
      else
        ⟨false, fun c => if col ∈ blue ∧ c = special then some (hidden special) else none,
          if col ∈ blue then some special else none⟩
    else blankCell q true

theorem positive_allOne {q : ℕ} (hidden : Fin q → Fin q) (blue : Finset (Fin q))
    (special : Fin q) : Pointer.allOne (positive hidden blue special) special := by
  intro row
  by_cases h : row = hidden special <;> simp [positive, h, blankCell]

theorem positive_good_iff {q : ℕ} (hidden : Fin q → Fin q) (blue : Finset (Fin q))
    (special col : Fin q) (hcol : col ≠ special) :
    Pointer.good (positive hidden blue special) (hidden special) special (hidden col) col ↔
      col ∈ blue := by
  unfold Pointer.good
  by_cases hblue : col ∈ blue <;> simp [positive, hcol, hblue]

theorem positive_valid {q : ℕ} (hidden : Fin q → Fin q) (blue : Finset (Fin q))
    (special : Fin q) (hspecial : special ∈ blue)
    (hcard : blue.card = (q - 1) / 2 + 1) :
    Pointer.Valid (positive hidden blue special) (hidden special) special hidden := by
  classical
  refine ⟨positive_allOne hidden blue special, ?_, ?_, ?_⟩
  · intro row hrow col hcol
    simp [positive, hrow, blankCell]
  · intro col hcol
    simp [positive, hcol]
  · have hset : (Finset.univ.filter (fun col => col ≠ special ∧
        Pointer.good (positive hidden blue special) (hidden special) special (hidden col) col)) =
        blue.erase special := by
      ext col
      by_cases hcol : col = special
      · simp [hcol]
      · simp [hcol, positive_good_iff hidden blue special col hcol]
    rw [hset, Finset.card_erase_of_mem hspecial, hcard]
    omega

theorem positive_value {q : ℕ} (hidden : Fin q → Fin q) (blue : Finset (Fin q))
    (special : Fin q) (hspecial : special ∈ blue)
    (hcard : blue.card = (q - 1) / 2 + 1) :
    Pointer.value (positive hidden blue special) = true :=
  (Pointer.value_eq_true_iff _).2
    ⟨hidden special, special, hidden, positive_valid hidden blue special hspecial hcard⟩

theorem pointer_has_zero_and_one (q : ℕ) (hq : 0 < q) :
    ∃ x₀ x₁ : PointerInput q, Pointer.value x₀ = false ∧ Pointer.value x₁ = true := by
  classical
  let hidden : Fin q → Fin q := fun _ => ⟨0, hq⟩
  have hsize : (q - 1) / 2 + 1 ≤ (Finset.univ : Finset (Fin q)).card := by simp; omega
  obtain ⟨blue, _, hblue⟩ := Finset.exists_subset_card_eq hsize
  have hnonempty : blue.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨special, hspecial⟩ := hnonempty
  exact ⟨negative hidden, positive hidden blue special, negative_value hidden,
    positive_value hidden blue special hspecial hblue⟩

/-- Every structured pointer input has a Boolean encoding when the cell
decoder is surjective. -/
theorem decodeInput_surjective {q : ℕ} {C : Type*}
    (decode : (C → Bool) → PointerCell q) (hdecode : Function.Surjective decode) :
    Function.Surjective (Pointer.decodeInput decode) := by
  classical
  intro x
  choose bits hbits using fun row col => hdecode (x row col)
  refine ⟨fun p => bits p.1.1 p.1.2 p.2, ?_⟩
  funext row col
  exact hbits row col

theorem encoded_has_zero_and_one {q : ℕ} {C : Type*} (hq : 0 < q)
    (decode : (C → Bool) → PointerCell q) (hdecode : Function.Surjective decode) :
    ∃ x₀ x₁, Pointer.encoded decode x₀ = false ∧ Pointer.encoded decode x₁ = true := by
  obtain ⟨x₀, x₁, hx₀, hx₁⟩ := pointer_has_zero_and_one q hq
  obtain ⟨bits₀, hbits₀⟩ := decodeInput_surjective decode hdecode x₀
  obtain ⟨bits₁, hbits₁⟩ := decodeInput_surjective decode hdecode x₁
  refine ⟨bits₀, bits₁, ?_, ?_⟩ <;> simp [Pointer.encoded, hbits₀, hbits₁, hx₀, hx₁]

theorem inner_has_zero_and_one {q : ℕ} {C : Type*} (hq : 0 < q)
    (decode : (C → Bool) → PointerCell q) (hdecode : Function.Surjective decode) :
    ∃ x₀ x₁, Pointer.inner decode x₀ = false ∧ Pointer.inner decode x₁ = true := by
  obtain ⟨bits₀, bits₁, hbits₀, hbits₁⟩ := encoded_has_zero_and_one hq decode hdecode
  refine ⟨fun p => bits₀ p.2, fun p => bits₁ p.2, ?_, ?_⟩
  · simp [Pointer.inner, comp, Pointer.majority, hbits₀]
  · simp [Pointer.inner, comp, Pointer.majority, hbits₁, hq]

theorem inner_R_pos {q : ℕ} {C : Type*} [Fintype C] (hq : 0 < q)
    (decode : (C → Bool) → PointerCell q) (hdecode : Function.Surjective decode) :
    0 < R (Pointer.inner decode) := by
  obtain ⟨x₀, x₁, hx₀, hx₁⟩ := inner_has_zero_and_one hq decode hdecode
  apply R_pos_of_nonconstant
  exact ⟨x₀, x₁, by rw [hx₀, hx₁]; decide⟩

/-- The blue set has one distinguished column, which becomes the special
cell. The other blue columns become good back-pointers. -/
abbrev ColorChoice (q : ℕ) :=
  {choice : Finset (Fin q) × Fin q //
    choice.2 ∈ choice.1 ∧ choice.1.card = (q - 1) / 2 + 1}

abbrev PositiveSample (q : ℕ) := (Fin q → Fin q) × ColorChoice q

def sampledPositive {q : ℕ} (sample : PositiveSample q) : PointerInput q :=
  positive sample.1 sample.2.1.1 sample.2.1.2

theorem sampledPositive_value {q : ℕ} (sample : PositiveSample q) :
    Pointer.value (sampledPositive sample) = true :=
  positive_value _ _ _ sample.2.2.1 sample.2.2.2

theorem colorChoice_nonempty (q : ℕ) (hq : 0 < q) : Nonempty (ColorChoice q) := by
  classical
  have hsize : (q - 1) / 2 + 1 ≤ (Finset.univ : Finset (Fin q)).card := by simp; omega
  obtain ⟨blue, _, hblue⟩ := Finset.exists_subset_card_eq hsize
  have hnonempty : blue.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨special, hspecial⟩ := hnonempty
  exact ⟨⟨(blue, special), hspecial, hblue⟩⟩

noncomputable def negativeWeight (q : ℕ) : PointerInput q → ℝ :=
  FiniteProbability.pushforward
    (FiniteProbability.uniformWeight (Fin q → Fin q)) negative

noncomputable def positiveWeight (q : ℕ) : PointerInput q → ℝ :=
  FiniteProbability.pushforward
    (FiniteProbability.uniformWeight (PositiveSample q)) sampledPositive

theorem negativeWeight_nonnegative (q : ℕ) :
    FiniteProbability.Nonnegative (negativeWeight q) :=
  FiniteProbability.pushforward_nonnegative (FiniteProbability.uniformWeight_nonnegative _) _

theorem positiveWeight_nonnegative (q : ℕ) :
    FiniteProbability.Nonnegative (positiveWeight q) :=
  FiniteProbability.pushforward_nonnegative (FiniteProbability.uniformWeight_nonnegative _) _

theorem negativeWeight_mass (q : ℕ) : FiniteProbability.mass (negativeWeight q) = 1 := by
  letI : Nonempty (Fin q → Fin q) := ⟨id⟩
  rw [negativeWeight, FiniteProbability.mass_pushforward, FiniteProbability.mass_uniformWeight]

theorem positiveWeight_mass (q : ℕ) (hq : 0 < q) :
    FiniteProbability.mass (positiveWeight q) = 1 := by
  letI : Nonempty (Fin q → Fin q) := ⟨id⟩
  letI : Nonempty (ColorChoice q) := colorChoice_nonempty q hq
  rw [positiveWeight, FiniteProbability.mass_pushforward, FiniteProbability.mass_uniformWeight]

theorem negativeWeight_support {q : ℕ} (x : PointerInput q)
    (hx : Pointer.value x = true) : negativeWeight q x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro hidden _
  rw [if_neg]
  intro h
  have := negative_value hidden
  rw [h, hx] at this
  cases this

theorem positiveWeight_support {q : ℕ} (x : PointerInput q)
    (hx : Pointer.value x = false) : positiveWeight q x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro sample _
  rw [if_neg]
  intro h
  have := sampledPositive_value sample
  rw [h, hx] at this
  cases this

end QueryComplexity.PointerDistributions
