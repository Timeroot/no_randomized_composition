import QueryComplexity.PointerLocalPosterior
import QueryComplexity.PosteriorMajority

open scoped BigOperators

namespace QueryComplexity.PointerDistributions

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A small total discovery count leaves at least one quarter of all blocks
among the negative blocks below the discovery threshold. -/
theorem many_low_discovery {q r : ℕ} (hq : 4 ≤ q) (hr : 0 < r)
    (negativeBlocks : Finset I) (hits : I → ℕ)
    (hnegative : q ≤ 2 * negativeBlocks.card + 1)
    (hbudget : 8 * (∑ i ∈ negativeBlocks, hits i) ≤ q * r) :
    q ≤ 4 * (negativeBlocks.filter (fun i => hits i < r)).card := by
  let low := negativeBlocks.filter (fun i => hits i < r)
  let high := negativeBlocks.filter (fun i => ¬ hits i < r)
  have hpartition : low.card + high.card = negativeBlocks.card :=
    Finset.card_filter_add_card_filter_not (s := negativeBlocks) _
  have hhigh : r * high.card ≤ ∑ i ∈ negativeBlocks, hits i := by
    calc
      _ = ∑ _i ∈ high, r := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ high, hits i := Finset.sum_le_sum fun i hi => by
        have h : ¬ hits i < r := (Finset.mem_filter.mp hi).2
        omega
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hbound : 8 * high.card ≤ q := by
    have hh : (8 * high.card) * r ≤ q * r := by nlinarith
    exact Nat.le_of_mul_le_mul_right hh hr
  change q ≤ 4 * low.card
  omega

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
  have hcount : q ≤ 4 * low.card := many_low_discovery (by omega) hr negativeBlocks hits hnegative hbudget
  have hlocal (i : I) (hi : i ∈ low) :
      1 / (4 * (5 : ℝ) ^ r) ≤ localPosterior trace i * (1 - localPosterior trace i) := by
    obtain ⟨hineg, hilow⟩ := Finset.mem_filter.mp hi
    have hraw := localPosterior_variance_lower hq trace i (reference i) (href i hineg)
      (by change 4 * hits i ≤ q; omega)
    refine le_trans ?_ hraw
    apply one_div_le_one_div_of_le (by positivity)
    apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt hilow)
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
