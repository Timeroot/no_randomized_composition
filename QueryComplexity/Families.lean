import QueryComplexity.FiniteEncoding
import QueryComplexity.ApproxIndexParameters
import QueryComplexity.Reindex
import QueryComplexity.PointerDistributions

/-! Concrete total functions for the proposed counterexample. This file
defines the functions; the quantitative query bounds are separate obligations. -/

namespace QueryComplexity.Construction

def seedLength (q : ℕ) : ℕ := Fintype.card (ApproxIndexCoordinates (ApproxIndex.seedSize q))

abbrev CoreCoordinates (q : ℕ) :=
  (Fin (seedLength q) × Fin (seedLength q)) × ApproxIndexCoordinates (ApproxIndex.seedSize q)

abbrev Witness (q : ℕ) := KleeneWitness (Fin (seedLength q)) (Fin (seedLength q))

noncomputable def coreCertificates (q : ℕ) :
    CertificateSystem (CoreCoordinates q → Bool) (Witness q) where
  valid x b w := kleeneValid (ApproxIndex.value (ApproxIndex.seedRadius q))
    (fun r c t => x ((r, c), t)) b w
  compatible := kleeneValid_compatible _

def payloadWidth (q c : ℕ) : ℕ := 1 + c * (seedLength q * seedLength q + 1)

noncomputable def outerDecoder (q c : ℕ) :
    CertificateDecoder (Fin c) (Witness q) (Fin (36 * payloadWidth q c) → Bool) :=
  privateAlphabetDecoder (payloadWidth q c) (by unfold payloadWidth; omega)
    (certificatePayload_card_bound (seedLength q) c)

theorem outerDecoder_surjective (q c : ℕ) : Function.Surjective (outerDecoder q c) :=
  privateAlphabetDecoder_surjective _ _ _

abbrev OuterCoordinates (q c : ℕ) :=
  CertificateCoordinates (Fin c) (CoreCoordinates q) (Fin (36 * payloadWidth q c))

noncomputable def outer (q c : ℕ) : BoolFn (OuterCoordinates q c) :=
  certificateBoolFn (coreCertificates q) (outerDecoder q c)

theorem outer_has_zero_and_one (q c : ℕ) :
    ∃ x y, outer q c x = false ∧ outer q c y = true := by
  apply certificateBoolFn_has_zero_and_one (coreCertificates q) (outerDecoder q c)
    (outerDecoder_surjective q c)
    (fun _ p => ApproxIndex.encode (ApproxIndex.seedRadius q) (fun _ => false) true p.2)
    (fun _ => true) (fun _ => Sum.inl id)
  intro i row
  exact ApproxIndex.value_encode _ _ _

theorem outer_R_pos (q c : ℕ) : 0 < R (outer q c) := by
  obtain ⟨x, y, hx, hy⟩ := outer_has_zero_and_one q c
  apply R_pos_of_nonconstant
  exact ⟨x, y, by rw [hx, hy]; decide⟩

def pointerPayloadWidth (q : ℕ) : ℕ := 1 + q * (q + 1)

noncomputable def pointerDecoder (q : ℕ) :
    (Fin (36 * pointerPayloadWidth q) → Bool) → PointerCell q :=
  privateAlphabetDecoder (pointerPayloadWidth q) (by unfold pointerPayloadWidth; omega)
    (pointerCell_card_bound q)

theorem pointerDecoder_surjective (q : ℕ) : Function.Surjective (pointerDecoder q) :=
  privateAlphabetDecoder_surjective _ _ _

abbrev InnerCoordinates (q : ℕ) :=
  Fin q × ((Fin q × Fin q) × Fin (36 * pointerPayloadWidth q))

noncomputable def inner (q : ℕ) : BoolFn (InnerCoordinates q) :=
  Pointer.inner (pointerDecoder q)

/-- Sparse indexing avoids logarithms in the eventual analytic comparison. -/
def scale (n : ℕ) : ℕ := 10 * 2 ^ (2 ^ n)
def pointerArity (n : ℕ) : ℕ := 2 ^ scale n - 1
def copies (n : ℕ) : ℕ := 100 * scale n
def outerArity (n : ℕ) : ℕ := Fintype.card (OuterCoordinates (pointerArity n) (copies n))
def innerArity (n : ℕ) : ℕ := Fintype.card (InnerCoordinates (pointerArity n))

noncomputable def F (n : ℕ) : BoolFn (Fin (outerArity n)) :=
  toFin (outer (pointerArity n) (copies n))

noncomputable def G (n : ℕ) : BoolFn (Fin (innerArity n)) :=
  toFin (inner (pointerArity n))

theorem F_R_pos (n : ℕ) : 0 < R (F n) := by
  rw [F, R_toFin]
  exact outer_R_pos _ _

theorem pointerArity_pos (n : ℕ) : 0 < pointerArity n := by
  have hs : 0 < scale n := by unfold scale; positivity
  have hp : 2 ≤ 2 ^ scale n := by
    simpa using (Nat.pow_le_pow_right (by omega : 0 < 2) (show 1 ≤ scale n by omega))
  unfold pointerArity
  omega

theorem G_R_pos (n : ℕ) : 0 < R (G n) := by
  rw [G, R_toFin]
  exact PointerDistributions.inner_R_pos (pointerArity_pos n) _ (pointerDecoder_surjective _)

end QueryComplexity.Construction
