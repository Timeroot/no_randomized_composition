import QueryComplexity.PointerMixture
import QueryComplexity.PointerCellTrees
import QueryComplexity.OraclePosteriors

open scoped BigOperators

namespace QueryComplexity.PointerDistributions

open FiniteProbability

variable {I : Type*} [Fintype I] [DecidableEq I] {q : ℕ}

noncomputable def localQueried (trace : List ((I × (Fin q × Fin q)) × PointerCell q)) (i : I) :
    Finset (Fin q × Fin q) := by
  classical
  exact Finset.univ.filter (fun coordinate => ∃ answer, ((i, coordinate), answer) ∈ trace)

omit [Fintype I] in
theorem localMatches_iff_observes
    (trace : List ((I × (Fin q × Fin q)) × PointerCell q)) (i : I)
    (reference : Fin q → Fin q)
    (href : OraclePosteriors.localMatches cellInput trace i (negative reference)) (x : PointerInput q) :
    OraclePosteriors.localMatches cellInput trace i x ↔
      Observes (localQueried trace i) x (negative reference) := by
  classical
  constructor
  · intro hx coordinate hcoordinate
    obtain ⟨answer, hentry⟩ : ∃ answer, ((i, coordinate), answer) ∈ trace := by
      simpa only [localQueried, Finset.mem_filter, Finset.mem_univ, true_and] using hcoordinate
    exact (hx _ hentry rfl).trans (href _ hentry rfl).symm
  · intro hx entry hentry hi
    rcases entry with ⟨⟨block, coordinate⟩, answer⟩
    dsimp only at hi
    subst block
    have hcoordinate : coordinate ∈ localQueried trace i := by
      simp only [localQueried, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨answer, hentry⟩
    exact (hx coordinate hcoordinate).trans (href _ hentry rfl)

theorem uniform_pushforward_event {A B : Type*} [Fintype A] [Fintype B]
    (mapping : A → B) (event : B → Prop) [DecidablePred event] :
    (∑ b, if event b then pushforward (uniformWeight A) mapping b else 0) =
      (Nat.card {a : A // event (mapping a)} : ℝ) / Nat.card A := by
  classical
  have h := sum_pushforward_mul (uniformWeight A) mapping (fun b => if event b then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [h]
  simp [uniformWeight, ← Finset.sum_filter, Nat.card_eq_fintype_card, Fintype.card_subtype,
    div_eq_mul_inv]

omit [Fintype I] in
theorem local_negative_mass
    (trace : List ((I × (Fin q × Fin q)) × PointerCell q)) (i : I)
    (reference : Fin q → Fin q)
    (href : OraclePosteriors.localMatches cellInput trace i (negative reference)) :
    mass (OraclePosteriors.localWeight (fun _ : I => negativeWeight q) cellInput trace i) =
      negativeObservationProbability (localQueried trace i) reference := by
  classical
  simp only [mass, OraclePosteriors.localWeight, localMatches_iff_observes trace i reference href,
    negativeWeight]
  exact uniform_pushforward_event negative (fun x => Observes (localQueried trace i) x (negative reference))

omit [Fintype I] in
theorem local_positive_mass
    (trace : List ((I × (Fin q × Fin q)) × PointerCell q)) (i : I)
    (reference : Fin q → Fin q)
    (href : OraclePosteriors.localMatches cellInput trace i (negative reference)) :
    mass (OraclePosteriors.localWeight (fun _ : I => positiveWeight q) cellInput trace i) =
      positiveObservationProbability (localQueried trace i) reference := by
  classical
  simp only [mass, OraclePosteriors.localWeight, localMatches_iff_observes trace i reference href,
    positiveWeight]
  exact uniform_pushforward_event sampledPositive
    (fun x => Observes (localQueried trace i) x (negative reference))

omit [Fintype I] [DecidableEq I] in
theorem local_mixed_mass
    (trace : List ((I × (Fin q × Fin q)) × PointerCell q)) (i : I) :
    mass (OraclePosteriors.localWeight (fun _ : I => mixedWeight q) cellInput trace i) =
      (mass (OraclePosteriors.localWeight (fun _ : I => negativeWeight q) cellInput trace i) +
        mass (OraclePosteriors.localWeight (fun _ : I => positiveWeight q) cellInput trace i)) / 2 := by
  classical
  simp only [mass, OraclePosteriors.localWeight, mixedWeight, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

omit [Fintype I] [DecidableEq I] in
theorem local_mixed_true_mass
    (trace : List ((I × (Fin q × Fin q)) × PointerCell q)) (i : I) :
    labelMass Pointer.value (OraclePosteriors.localWeight (fun _ : I => mixedWeight q) cellInput trace i) true =
      mass (OraclePosteriors.localWeight (fun _ : I => positiveWeight q) cellInput trace i) / 2 := by
  classical
  simp only [labelMass, mass, restrict, OraclePosteriors.localWeight, mixedWeight, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  cases hx : Pointer.value x
  · simp [positiveWeight_support x hx]
  · simp [negativeWeight_support x hx, ite_div]

noncomputable def localPosterior
    (trace : List ((I × (Fin q × Fin q)) × PointerCell q)) (i : I) : ℝ :=
  ProductPosteriors.posterior
    (OraclePosteriors.localWeight (fun _ : I => mixedWeight q) cellInput trace)
    (fun _ => Pointer.value) i

theorem localPosterior_eq_ratio
    (trace : List ((I × (Fin q × Fin q)) × PointerCell q)) (i : I)
    (reference : Fin q → Fin q)
    (href : OraclePosteriors.localMatches cellInput trace i (negative reference)) :
    localPosterior trace i =
      (positiveObservationProbability (localQueried trace i) reference /
        negativeObservationProbability (localQueried trace i) reference) /
      (1 + positiveObservationProbability (localQueried trace i) reference /
        negativeObservationProbability (localQueried trace i) reference) := by
  unfold localPosterior ProductPosteriors.posterior
  rw [local_mixed_true_mass, local_mixed_mass, local_negative_mass trace i reference href,
    local_positive_mass trace i reference href]
  have hn := negativeObservationProbability_pos (localQueried trace i) reference
  have hp : 0 ≤ positiveObservationProbability (localQueried trace i) reference := by
    unfold positiveObservationProbability
    positivity
  have hs : negativeObservationProbability (localQueried trace i) reference +
      positiveObservationProbability (localQueried trace i) reference ≠ 0 := by linarith
  field_simp

theorem observation_likelihood_le_one (hq : 2 ≤ q)
    (queried : Finset (Fin q × Fin q)) (reference : Fin q → Fin q) :
    positiveObservationProbability queried reference / negativeObservationProbability queried reference ≤ 1 := by
  rw [observation_likelihood_ratio hq]
  apply (div_le_one (by exact_mod_cast (Nat.choose_pos (show (q - 1) / 2 + 1 ≤ q by omega)))).2
  exact_mod_cast Nat.choose_le_choose ((q - 1) / 2 + 1) (Nat.sub_le q _)

/-- An actual negative-compatible local transcript leaves substantial
variance in its pointer label until many hidden cells have been found. -/
theorem localPosterior_variance_lower (hq : 5 ≤ q)
    (trace : List ((I × (Fin q × Fin q)) × PointerCell q)) (i : I)
    (reference : Fin q → Fin q)
    (href : OraclePosteriors.localMatches cellInput trace i (negative reference))
    (hdiscover : 4 * (discovered (localQueried trace i) reference).card ≤ q) :
    1 / (4 * (5 : ℝ) ^ (discovered (localQueried trace i) reference).card) ≤
      localPosterior trace i * (1 - localPosterior trace i) := by
  rw [localPosterior_eq_ratio trace i reference href]
  have h := PointerLikelihood.posterior_variance_lower
    (positiveObservationProbability (localQueried trace i) reference /
      negativeObservationProbability (localQueried trace i) reference)
    (1 / (5 : ℝ) ^ (discovered (localQueried trace i) reference).card)
    (by unfold positiveObservationProbability negativeObservationProbability; positivity)
    (observation_likelihood_le_one (by omega) _ _)
    (observation_likelihood_lower hq _ _ hdiscover)
  convert h using 1
  ring

omit [Fintype I] [DecidableEq I] in
theorem localPosterior_bounds
    (trace : List ((I × (Fin q × Fin q)) × PointerCell q)) (i : I) :
    0 ≤ localPosterior trace i ∧ localPosterior trace i ≤ 1 := by
  have hw : Nonnegative
      (OraclePosteriors.localWeight (fun _ : I => mixedWeight q) cellInput trace i) := by
    intro x
    unfold OraclePosteriors.localWeight
    split_ifs
    · exact mixedWeight_nonnegative q x
    · exact le_rfl
  have hm := mass_nonnegative hw
  constructor
  · exact div_nonneg (labelMass_nonnegative _ hw _) hm
  · unfold localPosterior ProductPosteriors.posterior
    by_cases hz : mass (OraclePosteriors.localWeight (fun _ : I => mixedWeight q) cellInput trace i) = 0
    · simp [hz]
    · apply (div_le_one (by positivity)).2
      exact labelMass_le_mass _ hw _

end QueryComplexity.PointerDistributions
