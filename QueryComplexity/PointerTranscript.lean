import QueryComplexity.PointerObservations
import QueryComplexity.PointerLikelihood
import QueryComplexity.PointedSetCounting

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
  exact PointerLikelihood.pointer_choose_avoid_probability_lower q _ hq hdiscover

end QueryComplexity.PointerDistributions
