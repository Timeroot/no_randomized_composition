import QueryComplexity.PointerFunction.Distributions
import QueryComplexity.LowerBounds.OraclePosteriors
import ForMathlib.Probability.PosteriorMajority
import QueryComplexity.PointerFunction.Majority.Transcript

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
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

omit [Fintype I] [DecidableEq I] in
theorem local_mixed_true_mass
    (trace : List ((I × (Fin q × Fin q)) × PointerCell q)) (i : I) :
    labelMass Pointer.value (OraclePosteriors.localWeight (fun _ : I => mixedWeight q) cellInput trace i) true =
      mass (OraclePosteriors.localWeight (fun _ : I => positiveWeight q) cellInput trace i) / 2 := by
  classical
  simp only [labelMass, mass, restrict, OraclePosteriors.localWeight, mixedWeight, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  cases hx : Pointer.value x
  · simp [positiveWeight_support x hx]
  · simp [negativeWeight_support x hx, ite_div]

noncomputable def localPosterior
    (trace : List ((I × (Fin q × Fin q)) × PointerCell q)) (i : I) : ℝ :=
  ProductPosteriors.posterior
    (OraclePosteriors.localWeight (fun _ : I => mixedWeight q) cellInput trace)
    (fun _ => Pointer.value) i

omit [Fintype I] in
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

omit [Fintype I] in
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
  have h := BernoulliPosterior.posterior_variance_lower
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

open scoped BigOperators

namespace QueryComplexity.PointerDistributions

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
/-- A sum bound forces many entries of a finite set below a threshold. -/
private theorem card_filter_lt_lower {q r : ℕ} (hq : 4 ≤ q) (hr : 0 < r)
    (B : Finset I) (f : I → ℕ)
    (hcard : q ≤ 2 * B.card + 1)
    (hbudget : 8 * (∑ i ∈ B, f i) ≤ q * r) :
    q ≤ 4 * (B.filter (fun i => f i < r)).card := by
  let low := B.filter (fun i => f i < r)
  let high := B.filter (fun i => ¬ f i < r)
  have hpartition : low.card + high.card = B.card :=
    Finset.card_filter_add_card_filter_not (s := B) _
  have hhigh : r * high.card ≤ ∑ i ∈ B, f i := by
    calc
      _ = ∑ _i ∈ high, r := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ high, f i := Finset.sum_le_sum fun i hi => by
        grind [Finset.mem_filter]
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hbound : 8 * high.card ≤ q := by nlinarith
  grind

/-- Deterministic assembly of the transcript's total posterior variance.
The only probabilistic input is the already proved local likelihood theorem. -/
theorem localPosterior_variance_sum_lower {q r : ℕ} (hq : 5 ≤ q) (hr : 0 < r)
    (hrsmall : 4 * r ≤ q)
    (trace : List ((I × (Fin q × Fin q)) × PointerCell q))
    (negativeBlocks : Finset I) (reference : I → Fin q → Fin q)
    (href : ∀ i ∈ negativeBlocks,
      OraclePosteriors.localMatches cellInput trace i (negative (reference i)))
    (hnegative : q ≤ 2 * negativeBlocks.card + 1)
    (hbudget : 8 * (∑ i ∈ negativeBlocks, (discovered (localQueried trace i) (reference i)).card) ≤ q * r) :
    (q : ℝ) / (16 * (5 : ℝ) ^ r) ≤
      PosteriorMajority.variance (localPosterior trace) := by
  classical
  let hits := fun i => (discovered (localQueried trace i) (reference i)).card
  let low := negativeBlocks.filter (fun i => hits i < r)
  have hcount : q ≤ 4 * low.card := card_filter_lt_lower (by omega) hr negativeBlocks hits hnegative hbudget
  have hlocal (i : I) (hi : i ∈ low) :
      1 / (4 * (5 : ℝ) ^ r) ≤ localPosterior trace i * (1 - localPosterior trace i) := by
    obtain ⟨hineg, hilow⟩ := Finset.mem_filter.mp hi
    have hraw := localPosterior_variance_lower hq trace i (reference i) (href i hineg)
      (by dsimp only [hits] at hilow; omega)
    exact (one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt hilow)) (by norm_num))).trans hraw
  calc
    (q : ℝ) / (16 * (5 : ℝ) ^ r) ≤ (low.card : ℝ) * (1 / (4 * (5 : ℝ) ^ r)) := by
      have hc : (q : ℝ) ≤ 4 * (low.card : ℝ) := by exact_mod_cast hcount
      apply (div_le_iff₀ (by positivity)).2
      field_simp
      nlinarith
    _ = ∑ i ∈ low, (1 / (4 * (5 : ℝ) ^ r)) := by simp [nsmul_eq_mul]
    _ ≤ ∑ i ∈ low, localPosterior trace i * (1 - localPosterior trace i) :=
      Finset.sum_le_sum hlocal
    _ ≤ PosteriorMajority.variance (localPosterior trace) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ low)
      intro i _ _
      obtain ⟨hp0, hp1⟩ := localPosterior_bounds trace i
      exact mul_nonneg hp0 (sub_nonneg.mpr hp1)

end QueryComplexity.PointerDistributions
