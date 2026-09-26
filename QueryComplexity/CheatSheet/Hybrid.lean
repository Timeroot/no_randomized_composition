import QueryComplexity.Encoding.AdaptivePrivacy
import QueryComplexity.CheatSheet.CellProjection

open scoped BigOperators

namespace QueryComplexity.CheatSheetHybrid

open FiniteProbability CellProjection

abbrev CellFiber (a : ℕ) (ha : 0 < a) (u : Fin a → Bool) :=
  {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = u}

variable {I T Witness Seed : Type*} [Fintype I] [DecidableEq I] [Fintype Seed]

def rawCells {a : ℕ} {ha : 0 < a} {u : Fin a → Bool}
    (Z : (I → Bool) → CellFiber a ha u) : (I → Bool) → Fin (36 * a) → Bool :=
  fun address => (Z address).1

omit [DecidableEq I] in
theorem rawCells_update {a : ℕ} {ha : 0 < a} {u : Fin a → Bool}
    (Z : (I → Bool) → CellFiber a ha u) (y : I → Bool) (z : CellFiber a ha u) :
    rawCells (Function.update Z y z) = Function.update (rawCells Z) y z.1 := by
  classical
  funext address
  by_cases h : address = y
  · subst address
    simp [rawCells]
  · simp [rawCells, Function.update_of_ne h]

omit [DecidableEq I] in
theorem pointwise_heavy_probability
    (a : ℕ) (ha : 0 < a) (D : (Fin a → Bool) → Bool × (I → Witness))
    (S : CertificateSystem (T → Bool) Witness)
    (A : FiniteRandomizedTree Seed (CertificateCoordinates I T (Fin (36 * a))) Bool)
    (hcorrect : ∀ x, (2 : ℝ) / 3 ≤ A.probability
      (fun b => b = certificateBoolFn S (fun z => D (BinaryCode.privateDecoder a ha z)) x) x)
    (cores : I → T → Bool) (y : I → Bool) (w w₀ : I → Witness)
    (hvalid : ∀ i, S.valid (cores i) (y i) (w i))
    (u v : Fin a → Bool) (hu : D u = (false, w₀)) (hv : D v = (true, w))
    (Z : (I → Bool) → CellFiber a ha u) :
    (1 : ℝ) / 6 ≤ ∑ s, A.weight s * average (fun z : CellFiber a ha u =>
      if 12 * a < DecisionTree.ownerCount cellOwner (A.tree s) y
        (certificateBitsOfInput ⟨cores, Function.update (rawCells Z) y z.1⟩)
      then (1 : ℝ) else 0) := by
  classical
  let B := A.substitute (cellSubstitution cores (rawCells Z) y)
  have hzero (z : CellFiber a ha u) : B.probability (fun b => b = true) z.1 ≤ 1 / 3 := by
    have hf : certificateBoolFn S (fun z => D (BinaryCode.privateDecoder a ha z))
        (certificateBitsOfInput ⟨cores, Function.update (rawCells Z) y z.1⟩) = false := by
      simp only [certificateBoolFn, certificateInputOfBits_bitsOfInput]
      apply CertificateInput.zeroFlags_reject
      intro address
      by_cases hy : address = y
      · subst address
        simp [z.2, hu]
      · simp [Function.update_of_ne hy, rawCells, (Z address).2, hu]
    have hc := hcorrect (certificateBitsOfInput ⟨cores, Function.update (rawCells Z) y z.1⟩)
    rw [hf, A.probability_false] at hc
    have hp : B.probability (fun b => b = true) z.1 =
        A.probability (fun b => b = true)
          (certificateBitsOfInput ⟨cores, Function.update (rawCells Z) y z.1⟩) := by simp [B]
    rw [hp]
    linarith
  have hone (z : CellFiber a ha v) : 2 / 3 ≤ B.probability (fun b => b = true) z.1 := by
    have hf : certificateBoolFn S (fun z => D (BinaryCode.privateDecoder a ha z))
        (certificateBitsOfInput ⟨cores, Function.update (rawCells Z) y z.1⟩) = true := by
      simp only [certificateBoolFn, certificateInputOfBits_bitsOfInput]
      rw [CertificateInput.cheatSheet_eq_true_iff]
      refine ⟨y, ?_⟩
      simpa [CertificateInput.AcceptsAt, z.2, hv] using hvalid
    have hc := hcorrect (certificateBitsOfInput ⟨cores, Function.update (rawCells Z) y z.1⟩)
    rw [hf] at hc
    simpa [B] using hc
  have hh := RandomizedPrivacy.privateDecoder_heavy_probability a ha u v B hzero hone
  simpa only [B, FiniteRandomizedTree.substitute, ← projectCell_cost, projectCell] using hh

/-- The all-invalid cell array is sampled independently of the core tuple.
Every correct algorithm must heavily query the correct address with constant
probability under this same fixed distribution on arrays. -/
theorem heavy_probability
    (a : ℕ) (ha : 0 < a) (D : (Fin a → Bool) → Bool × (I → Witness))
    (S : CertificateSystem (T → Bool) Witness)
    (A : FiniteRandomizedTree Seed (CertificateCoordinates I T (Fin (36 * a))) Bool)
    (hcorrect : ∀ x, (2 : ℝ) / 3 ≤ A.probability
      (fun b => b = certificateBoolFn S (fun z => D (BinaryCode.privateDecoder a ha z)) x) x)
    (cores : I → T → Bool) (y : I → Bool) (w w₀ : I → Witness)
    (hvalid : ∀ i, S.valid (cores i) (y i) (w i))
    (u v : Fin a → Bool) (hu : D u = (false, w₀)) (hv : D v = (true, w)) :
    (1 : ℝ) / 6 ≤ ∑ s, A.weight s *
      average (fun Z : (I → Bool) → CellFiber a ha u =>
        if 12 * a < DecisionTree.ownerCount cellOwner (A.tree s) y
          (certificateBitsOfInput ⟨cores, rawCells Z⟩) then (1 : ℝ) else 0) := by
  classical
  obtain ⟨z₀, hz₀⟩ := BinaryCode.privateDecoder_surjective a ha u
  letI : Nonempty (CellFiber a ha u) := ⟨⟨z₀, hz₀⟩⟩
  let f := fun Z : (I → Bool) → CellFiber a ha u => ∑ s, A.weight s *
    (if 12 * a < DecisionTree.ownerCount cellOwner (A.tree s) y
      (certificateBitsOfInput ⟨cores, rawCells Z⟩) then (1 : ℝ) else 0)
  have hp (Z : (I → Bool) → CellFiber a ha u) :
      (1 : ℝ) / 6 ≤ average (fun z : CellFiber a ha u => f (Function.update Z y z)) := by
    have h := pointwise_heavy_probability a ha D S A hcorrect cores y w w₀ hvalid u v hu hv Z
    simpa only [f, rawCells_update, average_sum, average_mul] using h
  have havg := average_le hp
  rw [average_const, average_resample] at havg
  simpa only [f, average_sum, average_mul] using havg

end QueryComplexity.CheatSheetHybrid
