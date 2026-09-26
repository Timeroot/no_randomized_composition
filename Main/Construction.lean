import QueryComplexity.ApproxIndex.FourthMoment
import Mathlib.Order.Filter.AtTopBot.Defs
import ForMathlib.LinearAlgebra.BinaryCode
import QueryComplexity.PointerFunction.Basic
import QueryComplexity.CheatSheet.Basic
import QueryComplexity.Basic
import QueryComplexity.PointerFunction.Distributions

/-! Parameters and Boolean functions for the separating family.
The polynomial approximate-index estimates feed the sparse outer and inner
constructions below; both functions have positive randomized query complexity. -/

open scoped BigOperators

namespace QueryComplexity.ApproxIndex

open FiniteProbability

def seedSize (q : ℕ) : ℕ := 10000 * q ^ 4
def seedRadius (q : ℕ) : ℕ := 5000 * q ^ 4 - 500 * q ^ 3
def seedBudget (q : ℕ) : ℕ := 250 * q ^ 3
noncomputable def seedEta (q : ℕ) : ℝ := 16 / (16875 * (q : ℝ) ^ 4)

theorem seedRadius_sub_le (q : ℕ) : 500 * q ^ 3 ≤ 5000 * q ^ 4 := by
  cases q with
  | zero => norm_num
  | succ q => gcongr <;> omega

private theorem seed_gap (q : ℕ) :
    (seedSize q : ℝ) - 2 * (seedRadius q : ℝ) - (seedBudget q : ℝ) = 750 * (q : ℝ) ^ 3 := by
  unfold seedSize seedRadius seedBudget
  rw [Nat.cast_sub (seedRadius_sub_le q)]
  push_cast
  ring

private theorem seed_gap_pos (q : ℕ) (hq : 0 < q) :
    0 < (seedSize q : ℝ) - 2 * (seedRadius q : ℝ) - (seedBudget q : ℝ) := by
  rw [seed_gap q]
  have : (0 : ℝ) < q := by exact_mod_cast hq
  positivity

private theorem seedEta_eq_fourth_moment (q : ℕ) (hq : 0 < q) :
    3 * (seedSize q : ℝ) ^ 2 /
      ((seedSize q : ℝ) - 2 * (seedRadius q : ℝ) - (seedBudget q : ℝ)) ^ 4 = seedEta q := by
  rw [seed_gap q]
  simp only [seedSize, seedEta, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  field_simp
  ring

theorem seed_ballSliceBound (q : ℕ) (hq : 0 < q) :
    @BallSliceBound (seedSize q) (seedRadius q) (seedBudget q) (seedEta q) := by
  rw [← seedEta_eq_fourth_moment q hq]
  exact ballSliceBound_fourth_moment (seedRadius q) (seedBudget q) (seed_gap_pos q hq)

theorem seedEta_nonnegative (q : ℕ) : 0 ≤ seedEta q := by
  unfold seedEta
  positivity

theorem seedBudget_mul_eta (q : ℕ) (hq : 0 < q) :
    (seedBudget q : ℝ) * seedEta q = 32 / (135 * (q : ℝ)) := by
  simp only [seedBudget, seedEta, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  field_simp
  ring

end QueryComplexity.ApproxIndex

/-! The concrete total Boolean families and their basic parameter properties.
The quantitative upper and lower bounds are proved in the other Main modules. -/

namespace QueryComplexity.Construction

open FiniteEncoding

def seedLength (q : ℕ) : ℕ := Fintype.card (ApproxIndexCoordinates (ApproxIndex.seedSize q))

theorem seedLength_pos (q : ℕ) : 0 < seedLength q := Fintype.card_pos

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

/-! Elementary properties of the sparse parameter sequence. -/

open Filter

theorem scale_ge_ten (n : ℕ) : 10 ≤ scale n := by
  have h : 1 ≤ 2 ^ (2 ^ n) := Nat.one_le_pow _ _ (by omega)
  unfold scale
  omega

theorem pointerArity_ge_three (n : ℕ) : 3 ≤ pointerArity n := by
  have hs : 2 ≤ scale n := (by omega : 2 ≤ 10).trans (scale_ge_ten n)
  have hp : 4 ≤ 2 ^ scale n := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hs
  unfold pointerArity
  omega

theorem pointerArity_le_pow_scale (n : ℕ) : pointerArity n ≤ 2 ^ scale n := Nat.sub_le _ _

theorem index_le_scale (n : ℕ) : n ≤ scale n := by
  have h₁ := Nat.lt_two_pow_self (n := n)
  have h₂ := Nat.lt_two_pow_self (n := 2 ^ n)
  unfold scale
  omega

theorem eventually_scale_ge (N : ℕ) : ∀ᶠ n in atTop, N ≤ scale n :=
  (eventually_ge_atTop N).mono (fun n hn => hn.trans (index_le_scale n))

theorem scale_cast (n : ℕ) : (scale n : ℝ) = 10 * (2 : ℝ) ^ (2 ^ n) := by
  simp only [scale, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]

theorem pointerArity_odd (n : ℕ) : Odd (pointerArity n) := by
  have hs : scale n ≠ 0 := by have := scale_ge_ten n; omega
  have hp : Even (2 ^ scale n) := (show Even (2 : ℕ) by decide).pow_of_ne_zero hs
  apply (Nat.odd_sub' (Nat.one_le_pow _ _ (by omega))).mpr
  simpa using hp

end QueryComplexity.Construction
