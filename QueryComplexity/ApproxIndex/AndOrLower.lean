import QueryComplexity.ApproxIndex.Simulation
import QueryComplexity.LowerBounds.AndOr
import QueryComplexity.LowerBounds.DirectProduct
import QueryComplexity.CheatSheet.Basic

/-! An explicit hard distribution for the AND--OR core of approximate-index
seeds. All sampled inputs satisfy the partial core's certificate promise. -/

open scoped BigOperators

namespace QueryComplexity.CoreLower

open FiniteProbability DirectProduct ApproxIndex DecisionTree

variable {Row Col : Type*} [Fintype Row] [Fintype Col] [DecidableEq Row] [DecidableEq Col]
variable {k : ℕ}

abbrev Coordinates (Row Col : Type*) (k : ℕ) := (Row × Col) × ApproxIndexCoordinates k

noncomputable def extension : BoolFn (Coordinates Row Col k) := by
  classical
  exact fun x => decide (∀ r : Row, ∃ c : Col,
    ApproxIndex.extension (fun t => x ((r, c), t)) = true)

omit [DecidableEq Row] [DecidableEq Col] in
theorem extension_encodeBlocks (radius : ℕ) (a : (Row × Col) → Fin k → Bool)
    (z : Row × Col → Bool) :
    extension (encodeBlocks radius a z) = decide (∀ r : Row, ∃ c : Col, z (r, c) = true) := by
  classical
  have he (i : Row × Col) : ApproxIndex.extension (encode radius (a i) (z i)) = z i :=
    ApproxIndex.extension_correct radius _ _ (value_encode radius _ _)
  simp only [extension, encodeBlocks, he]

abbrev Sample (Row Col : Type*) (k : ℕ) :=
  ((Row × Col) → Fin k → Bool) × ((Row → Col) × (Row × Bool))

def sampleInput (radius : ℕ) (p : Sample Row Col k) : Coordinates Row Col k → Bool :=
  encodeBlocks radius p.1
    (if p.2.2.2 then AndOrLower.positive p.2.1 else AndOrLower.negative p.2.1 p.2.2.1)

theorem sampleInput_label (radius : ℕ) (p : Sample Row Col k) :
    extension (sampleInput radius p) = p.2.2.2 := by
  classical
  rcases p with ⟨a, positions, row, bit⟩
  cases bit
  · simp only [sampleInput, Bool.false_eq_true, if_false]
    rw [extension_encodeBlocks]
    apply decide_eq_false
    intro h
    obtain ⟨c, hc⟩ := h row
    simp [AndOrLower.negative, replaceBlock] at hc
  · rw [sampleInput, if_pos rfl, extension_encodeBlocks]
    apply decide_eq_true
    intro r
    exact ⟨positions r, by simp [AndOrLower.positive, AndOrLower.oneHot]⟩

omit [Fintype Row] [Fintype Col] in
theorem sampleInput_valid (radius : ℕ) (p : Sample Row Col k) :
    ∃ witness : KleeneWitness Row Col,
      kleeneValid (ApproxIndex.value radius)
        (fun r c t => sampleInput radius p ((r, c), t)) p.2.2.2 witness := by
  rcases p with ⟨a, positions, row, bit⟩
  cases bit
  · refine ⟨.inr row, ?_⟩
    intro c
    have he : AndOrLower.negative positions row (row, c) = false := by
      simp [AndOrLower.negative, replaceBlock]
    simpa only [sampleInput, Bool.false_eq_true, if_false, encodeBlocks, he] using
      value_encode radius (a (row, c)) false
  · refine ⟨.inl positions, ?_⟩
    intro r
    have he : AndOrLower.positive positions (r, positions r) = true := by
      simp [AndOrLower.positive, AndOrLower.oneHot]
    simpa only [sampleInput, if_true, encodeBlocks, he] using
      value_encode radius (a (r, positions r)) true

noncomputable def hardWeight (radius : ℕ) : Weight (Coordinates Row Col k → Bool) :=
  pushforward (uniformWeight (Sample Row Col k)) (sampleInput radius)

theorem hardWeight_nonnegative (radius : ℕ) : Nonnegative (@hardWeight Row Col _ _ _ _ k radius) :=
  pushforward_nonnegative (uniformWeight_nonnegative _) _

theorem mass_hardWeight [Nonempty Row] [Nonempty Col] (radius : ℕ) :
    mass (@hardWeight Row Col _ _ _ _ k radius) = 1 := by
  rw [hardWeight, mass_pushforward, mass_uniformWeight]

theorem hardWeight_score (radius : ℕ) (tree : DecisionTree (Coordinates Row Col k) Bool) :
    score extension (hardWeight radius) tree =
      average (fun p : Sample Row Col k =>
        if tree.eval (sampleInput radius p) = p.2.2.2 then (1 : ℝ) else 0) := by
  have hp := sum_pushforward_mul (uniformWeight (Sample Row Col k)) (sampleInput radius)
    (fun x => if tree.eval x = extension x then (1 : ℝ) else 0)
  have he : score extension (hardWeight radius) tree =
      ∑ x, hardWeight radius x * (if tree.eval x = extension x then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  rw [he, hardWeight, hp]
  simp only [average, sampleInput_label]

theorem hardWeight_eq_zero_of_invalid (radius : ℕ) (x : Coordinates Row Col k → Bool)
    (h : ∀ b witness, ¬ kleeneValid (ApproxIndex.value radius)
      (fun r c t => x ((r, c), t)) b witness) : hardWeight radius x = 0 := by
  classical
  unfold hardWeight pushforward
  apply Finset.sum_eq_zero
  intro p _
  have he : sampleInput radius p ≠ x := by
    intro he
    obtain ⟨witness, hw⟩ := sampleInput_valid radius p
    apply h p.2.2.2 witness
    simpa only [he] using hw
  simp [he]

theorem hardWeight_score_le [Nonempty Row] [Nonempty Col]
    (radius budget Q : ℕ) (η : ℝ) (hbudget : 0 < budget) (hη : 0 ≤ η)
    (hball : @BallSliceBound k radius budget η)
    (tree : DecisionTree (Coordinates Row Col k) Bool) (hdepth : tree.depth ≤ Q) :
    score extension (hardWeight radius) tree ≤
      1 / 2 + (Q : ℝ) / ((budget : ℝ) * ((Fintype.card Row : ℝ) * Fintype.card Col)) +
        (budget : ℝ) * η := by
  let N : ℝ := (Fintype.card Row : ℝ) * Fintype.card Col
  have hN : 0 < N := by
    dsimp [N]
    exact mul_pos (by exact_mod_cast Fintype.card_pos) (by exact_mod_cast Fintype.card_pos)
  have hb : (0 : ℝ) < budget := by exact_mod_cast hbudget
  have houter (a : (Row × Col) → Fin k → Bool) :=
    AndOrLower.andOr_average_success_bound (simulatedTree radius tree a)
  have havg := average_le houter
  simp only [average_add, average_const, average_div] at havg
  have hcost :
      average (fun a : (Row × Col) → Fin k → Bool => average (fun positions : Row → Col =>
        ((simulatedTree radius tree a).queryCost (AndOrLower.positive positions) : ℝ))) ≤
      (Q : ℝ) / (budget : ℝ) + N * ((budget : ℝ) * η) := by
    rw [average_comm]
    calc
      _ ≤ average (fun _ : Row → Col => (Q : ℝ) / (budget : ℝ) + N * ((budget : ℝ) * η)) := by
        apply average_le
        intro positions
        simpa only [N, Fintype.card_prod, Nat.cast_mul] using
          simulatedTree_expected_cost_le radius budget Q η hbudget hη hball tree
            (AndOrLower.positive positions) hdepth
      _ = _ := average_const _
  rw [hardWeight_score]
  simp only [average_prod, sampleInput]
  have hmain :
      average (fun a : (Row × Col) → Fin k → Bool =>
        average (fun positions : Row → Col => average (fun row : Row => average (fun bit : Bool =>
          if tree.eval (encodeBlocks radius a
            (if bit then AndOrLower.positive positions else AndOrLower.negative positions row)) = bit
            then (1 : ℝ) else 0)))) ≤
        1 / 2 + ((Q : ℝ) / (budget : ℝ) + N * ((budget : ℝ) * η)) / N := by
    have havg' := havg.trans (add_le_add (le_refl ((1 : ℝ) / 2))
      (div_le_div_of_nonneg_right hcost (le_of_lt hN)))
    simpa only [simulatedTree_eval, AndOrLower.scenario, N] using havg'
  refine hmain.trans_eq ?_
  dsimp [N] at *
  field_simp
  ring

omit [DecidableEq Row] [DecidableEq Col] in
theorem extension_correct_certificate (radius : ℕ) (x : Coordinates Row Col k → Bool)
    (b : Bool) (witness : KleeneWitness Row Col)
    (h : kleeneValid (ApproxIndex.value radius) (fun r c t => x ((r, c), t)) b witness) :
    extension x = b := by
  classical
  cases b with
  | false =>
    cases witness with
    | inl select => exact h.elim
    | inr row =>
      unfold extension
      apply decide_eq_false
      intro he
      obtain ⟨c, hc⟩ := he row
      have hz := ApproxIndex.extension_correct radius _ false (h c)
      rw [hz] at hc
      contradiction
  | true =>
    cases witness with
    | inl select =>
      unfold extension
      apply decide_eq_true
      intro row
      exact ⟨select row, ApproxIndex.extension_correct radius _ true (h row)⟩
    | inr row => exact h.elim

theorem hardWeight_supported (radius : ℕ) (x : Coordinates Row Col k → Bool)
    (h : hardWeight radius x ≠ 0) :
    ∃ witness, kleeneValid (ApproxIndex.value radius)
      (fun r c t => x ((r, c), t)) (extension x) witness := by
  classical
  have hex : ∃ b witness, kleeneValid (ApproxIndex.value radius)
      (fun r c t => x ((r, c), t)) b witness := by
    by_contra hn
    apply h
    apply hardWeight_eq_zero_of_invalid
    simpa only [not_exists] using hn
  obtain ⟨b, witness, hw⟩ := hex
  exact ⟨witness, by rw [extension_correct_certificate radius x b witness hw]; exact hw⟩

end QueryComplexity.CoreLower
