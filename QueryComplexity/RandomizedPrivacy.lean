import QueryComplexity.AdaptivePrivacy
import QueryComplexity.Algorithms

open scoped BigOperators

namespace QueryComplexity.RandomizedPrivacy

open FiniteProbability AdaptivePrivacy

theorem probability_weighted_sum {Seed T Output : Type*} [Fintype Seed]
    (A : FiniteRandomizedTree Seed T Output) (event : Output → Prop) [DecidablePred event] (x : T → Bool) :
    A.probability event x =
      ∑ s, A.weight s * (if event ((A.tree s).eval x) then (1 : ℝ) else 0) := by
  classical
  unfold FiniteRandomizedTree.probability
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : event ((A.tree s).eval x) <;> simp [h]

theorem privateDecoder_heavy_probability {Seed : Type*} [Fintype Seed]
    (a : ℕ) (ha : 0 < a) (u v : Fin a → Bool)
    (A : FiniteRandomizedTree Seed (Fin (36 * a)) Bool)
    (hzero : ∀ x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = u},
      A.probability (fun b => b = true) x.1 ≤ 1 / 3)
    (hone : ∀ x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = v},
      2 / 3 ≤ A.probability (fun b => b = true) x.1) :
    (1 : ℝ) / 6 ≤ ∑ s, A.weight s *
      average (fun x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = u} =>
        if 12 * a < (A.tree s).queryCost x.1 then (1 : ℝ) else 0) := by
  classical
  have hnonempty (w : Fin a → Bool) :
      Nonempty {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = w} := by
    obtain ⟨x, hx⟩ := BinaryCode.privateDecoder_surjective a ha w
    exact ⟨⟨x, hx⟩⟩
  letI := hnonempty u
  letI := hnonempty v
  have hneg : average (fun x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = u} =>
      A.probability (fun b => b = true) x.1) ≤ 1 / 3 := by
    exact (average_le hzero).trans_eq (average_const _)
  have hpos : 2 / 3 ≤ average (fun x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = v} =>
      A.probability (fun b => b = true) x.1) := by
    exact (average_const _).symm.trans_le (average_le hone)
  have he (w : Fin a → Bool) :
      average (fun x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = w} =>
        A.probability (fun b => b = true) x.1) =
      ∑ s, A.weight s * average
        (fun x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = w} =>
          if (A.tree s).eval x.1 = true then (1 : ℝ) else 0) := by
    simp_rw [probability_weighted_sum, average_sum, average_mul]
  have hh (s : Seed) := privateDecoder_average_hybrid a ha u v (A.tree s)
  have hd (s : Seed) :
      average (fun x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = v} =>
        if (A.tree s).eval x.1 = true then (1 : ℝ) else 0) -
      average (fun x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = u} =>
        if (A.tree s).eval x.1 = true then (1 : ℝ) else 0) ≤
      2 * average (fun x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = u} =>
        if 12 * a < (A.tree s).queryCost x.1 then (1 : ℝ) else 0) := by
    have h := hh s
    rw [abs_sub_comm] at h
    exact (le_abs_self _).trans h
  have hw := Finset.sum_le_sum (s := Finset.univ)
    (fun s _ => mul_le_mul_of_nonneg_left (hd s) (A.weight_nonneg s))
  simp only [mul_sub, Finset.sum_sub_distrib] at hw
  rw [he u] at hneg
  rw [he v] at hpos
  have hscale : (∑ s, A.weight s * (2 *
      average (fun x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = u} =>
        if 12 * a < (A.tree s).queryCost x.1 then (1 : ℝ) else 0))) =
      2 * ∑ s, A.weight s * average
        (fun x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = u} =>
          if 12 * a < (A.tree s).queryCost x.1 then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hscale] at hw
  linarith

end QueryComplexity.RandomizedPrivacy
