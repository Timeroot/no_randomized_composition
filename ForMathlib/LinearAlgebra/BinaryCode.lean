import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Ring.Finset
import ForMathlib.LinearAlgebra.Cosets
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Fintype.EquivFin

/-! Binary linear codes with private coordinate marginals and finite-alphabet decoders. -/

section

/-! Boolean coordinates carry their usual two-element field structure.
Addition is XOR and multiplication is AND. -/

namespace Bool

instance boolNoZeroDivisors : NoZeroDivisors Bool where
  eq_zero_or_eq_zero_of_mul_eq_zero := by decide

instance boolIsDomain : IsDomain Bool := NoZeroDivisors.to_isDomain Bool

noncomputable instance boolField : Field Bool := Fintype.fieldOfDomain Bool

end Bool

end

section

/-! Binary linear codes with large dual distance, obtained by finite counting,
and uniform low-coordinate marginals of their fibers. -/

open scoped BigOperators

namespace BinaryCode

def weight {I : Type*} [Fintype I] (x : I → Bool) : ℕ :=
  (Finset.univ.filter (fun i => x i = true)).card

theorem weight_generating_function {I : Type*} [Fintype I] [DecidableEq I] (r : ℝ) :
    ∑ x : I → Bool, r ^ weight x = (1 + r) ^ Fintype.card I := by
  classical
  have hprod (x : I → Bool) : (∏ i, if x i = true then r else 1) = r ^ weight x := by
    rw [← Finset.prod_filter]
    simp [weight]
  calc
    ∑ x : I → Bool, r ^ weight x = ∑ x : I → Bool, ∏ i, if x i = true then r else 1 := by
      simp only [hprod]
    _ = ∏ _i : I, ∑ b : Bool, if b = true then r else 1 :=
      (Fintype.prod_sum (fun (_ : I) (b : Bool) => if b = true then r else 1)).symm
    _ = (1 + r) ^ Fintype.card I := by simp [add_comm]

/-- A Chernoff counting bound derived from the exact generating function. -/
theorem ball_card_bound {I : Type*} [Fintype I] [DecidableEq I] (d : ℕ) :
    ((Finset.univ.filter (fun x : I → Bool => weight x ≤ d)).card : ℝ) *
      (1 / 2 : ℝ) ^ d ≤ (3 / 2 : ℝ) ^ Fintype.card I := by
  classical
  calc
    ((Finset.univ.filter (fun x : I → Bool => weight x ≤ d)).card : ℝ) * (1 / 2 : ℝ) ^ d =
        ∑ x ∈ Finset.univ.filter (fun x : I → Bool => weight x ≤ d), (1 / 2 : ℝ) ^ d := by simp
    _ ≤ ∑ x ∈ Finset.univ.filter (fun x : I → Bool => weight x ≤ d), (1 / 2 : ℝ) ^ weight x := by
      refine Finset.sum_le_sum fun x hx => ?_
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Finset.mem_filter.mp hx).2
    _ ≤ ∑ x : I → Bool, (1 / 2 : ℝ) ^ weight x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro x _ _
      positivity
    _ = (3 / 2 : ℝ) ^ Fintype.card I := by
      rw [weight_generating_function]
      norm_num

/-- Taking a prescribed linear combination of the rows of a matrix is itself
a linear map on the matrix space. -/
noncomputable def rowCombination {I J : Type*} [Fintype I] (v : I → Bool) :
    (I → J → Bool) →ₗ[Bool] (J → Bool) where
  toFun M j := ∑ i, v i * M i j
  map_add' M N := by
    ext j
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c M := by
    ext j
    simp [Finset.mul_sum, mul_left_comm]

/-- A nonzero row combination is uniformly distributed when the matrix is:
the algebraic input for this assertion is surjectivity. -/
theorem rowCombination_surjective {I J : Type*} [Fintype I] [DecidableEq I]
    (v : I → Bool) (hv : v ≠ 0) : Function.Surjective (rowCombination (J := J) v) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hvi : v i = true := Bool.eq_true_of_not_eq_false hi
  intro y
  refine ⟨fun r => if r = i then y else 0, ?_⟩
  ext j
  simp only [rowCombination, LinearMap.coe_mk, AddHom.coe_mk, ite_apply, Pi.zero_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hvi]
  exact one_mul _

private theorem code_counting_strict (a : ℕ) (ha : 0 < a) :
    (2 : ℝ) ^ a * (3 / 2 : ℝ) ^ (36 * a) <
      (2 : ℝ) ^ (36 * a) * (1 / 2 : ℝ) ^ (12 * a) := by
  rw [pow_mul, pow_mul, pow_mul, ← mul_pow, ← mul_pow]
  apply pow_lt_pow_left₀ (by norm_num) (by positivity) (by omega)

/-- The bad Hamming ball is small enough to union-bound over all row
coefficient vectors. -/
private theorem ball_small_enough (a : ℕ) (ha : 0 < a) :
    2 ^ a * (Finset.univ.filter
      (fun x : Fin (36 * a) → Bool => weight x ≤ 12 * a)).card < 2 ^ (36 * a) := by
  let B := (Finset.univ.filter
    (fun x : Fin (36 * a) → Bool => weight x ≤ 12 * a)).card
  have hb : (B : ℝ) * (1 / 2 : ℝ) ^ (12 * a) ≤ (3 / 2 : ℝ) ^ (36 * a) := by
    simpa [B] using ball_card_bound (I := Fin (36 * a)) (12 * a)
  have hp : 0 < (1 / 2 : ℝ) ^ (12 * a) := by positivity
  have hmul : ((2 : ℝ) ^ a * B) * (1 / 2 : ℝ) ^ (12 * a) <
      (2 : ℝ) ^ (36 * a) * (1 / 2 : ℝ) ^ (12 * a) := by
    calc
      _ ≤ (2 : ℝ) ^ a * (3 / 2 : ℝ) ^ (36 * a) := by
        nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ (2 : ℝ) ^ a by positivity)]
      _ < _ := code_counting_strict a ha
  have hreal := lt_of_mul_lt_mul_right hmul hp.le
  exact_mod_cast hreal

/-- A full-row-rank binary matrix with constant relative rowspace distance
exists at every positive payload length. -/
theorem exists_matrix (a : ℕ) (ha : 0 < a) :
    ∃ M : Fin a → Fin (36 * a) → Bool,
      ∀ v : Fin a → Bool, v ≠ 0 → 12 * a < weight (rowCombination v M) := by
  classical
  let Bad : Finset (Fin (36 * a) → Bool) :=
    Finset.univ.filter (fun x => weight x ≤ 12 * a)
  let Coeff := {v : Fin a → Bool // v ≠ 0}
  have hc : Nat.card Coeff ≤ 2 ^ a := by
    simp [Coeff, Nat.card_eq_fintype_card]
  have hsmall : Nat.card Coeff * Bad.card < Nat.card (Fin (36 * a) → Bool) := by
    have hb := (Nat.mul_le_mul_right Bad.card hc).trans_lt (ball_small_enough a ha)
    simpa [Bad, Nat.card_eq_fintype_card] using hb
  obtain ⟨M, hM⟩ := Cosets.exists_avoiding_bad_images
    (fun v : Coeff => (rowCombination (J := Fin (36 * a)) v.1).toAddMonoidHom)
    (fun v => rowCombination_surjective v.1 v.2) Bad hsmall
  refine ⟨M, fun v hv => ?_⟩
  have h := hM (⟨v, hv⟩ : Coeff)
  simpa [Bad] using h

noncomputable def dualCoefficients {I : Type*} [Fintype I] [DecidableEq I]
    (f : Module.Dual Bool (I → Bool)) : I → Bool :=
  fun i => f (Pi.single i 1)

theorem dual_expansion {I : Type*} [Fintype I] [DecidableEq I]
    (f : Module.Dual Bool (I → Bool)) (x : I → Bool) :
    f x = ∑ i, dualCoefficients f i * x i := by
  have hx : x = ∑ i, x i • (Pi.single i (1 : Bool) : I → Bool) := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  conv_lhs => rw [hx]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [dualCoefficients, mul_comm]

theorem dualCoefficients_ne_zero {I : Type*} [Fintype I] [DecidableEq I]
    (f : Module.Dual Bool (I → Bool)) (hf : f ≠ 0) : dualCoefficients f ≠ 0 := by
  intro h
  apply hf
  apply LinearMap.ext
  intro x
  rw [dual_expansion]
  simp [h]

theorem dual_composition_support {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (M : I → J → Bool) (f : Module.Dual Bool (I → Bool)) :
    (Cosets.dualSupport (f.comp (Matrix.toLin' M))).card =
      weight (rowCombination (dualCoefficients f) M) := by
  apply congrArg Finset.card
  ext j
  simp only [Cosets.dualSupport, Finset.mem_filter, Finset.mem_univ,
    true_and, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  rw [dual_expansion]
  simp only [rowCombination, LinearMap.coe_mk, AddHom.coe_mk, Matrix.col_apply]
  cases (∑ i, dualCoefficients f i * M i j) <;> decide

/-- The decoder supplied by the finite counting argument has the exact
dual-distance property used in the privacy theorem. -/
theorem exists_private_linear_decoder (a : ℕ) (ha : 0 < a) :
    ∃ H : (Fin (36 * a) → Bool) →ₗ[Bool] (Fin a → Bool),
      ∀ f : Module.Dual Bool (Fin a → Bool), f ≠ 0 →
        12 * a + 1 ≤ (Cosets.dualSupport (f.comp H)).card := by
  obtain ⟨M, hM⟩ := exists_matrix a ha
  refine ⟨Matrix.toLin' M, fun f hf => ?_⟩
  rw [dual_composition_support]
  exact hM (dualCoefficients f) (dualCoefficients_ne_zero f hf)

noncomputable def privateDecoder (a : ℕ) (ha : 0 < a) :
    (Fin (36 * a) → Bool) →ₗ[Bool] (Fin a → Bool) :=
  Classical.choose (exists_private_linear_decoder a ha)

theorem privateDecoder_distance (a : ℕ) (ha : 0 < a)
    (f : Module.Dual Bool (Fin a → Bool)) (hf : f ≠ 0) :
    12 * a + 1 ≤ (Cosets.dualSupport (f.comp (privateDecoder a ha))).card :=
  Classical.choose_spec (exists_private_linear_decoder a ha) f hf

theorem privateDecoder_surjective (a : ℕ) (ha : 0 < a) :
    Function.Surjective (privateDecoder a ha) :=
  Cosets.surjective_of_nonzero_dual_distance _ (12 * a + 1) (by omega)
    (privateDecoder_distance a ha)

theorem privateDecoder_uniform (a : ℕ) (ha : 0 < a)
    (s : Finset (Fin (36 * a))) (hs : s.card ≤ 12 * a)
    (payload : Fin a → Bool) (observed : s → Bool) :
    (Nat.card {x : Fin (36 * a) → Bool // privateDecoder a ha x = payload ∧
        Cosets.restrictCoordinates s x = observed} : ℝ) /
        (Nat.card {x : Fin (36 * a) → Bool // privateDecoder a ha x = payload} : ℝ) =
      1 / (Nat.card (s → Bool) : ℝ) :=
  Cosets.uniform_coordinates_of_dual_distance _ (12 * a + 1) (by omega)
    (privateDecoder_distance a ha) s (by omega) payload observed

end BinaryCode

end

section

/-! Total surjections from Boolean vectors onto nonempty finite alphabets. -/

namespace FiniteEncoding

/-- Decode enough bits onto an arbitrary nonempty finite alphabet. -/
noncomputable def finiteDecode {Y : Type*} [Fintype Y] [Nonempty Y]
    (a : ℕ) (hcard : Fintype.card Y ≤ 2 ^ a) : (Fin a → Bool) → Y :=
  let e : Y ↪ (Fin a → Bool) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le
      (show Fintype.card Y ≤ Fintype.card (Fin a → Bool) by simpa using hcard))
  Function.invFun e

theorem finiteDecode_surjective {Y : Type*} [Fintype Y] [Nonempty Y]
    (a : ℕ) (hcard : Fintype.card Y ≤ 2 ^ a) :
    Function.Surjective (finiteDecode a hcard) :=
  Function.invFun_surjective (Function.Embedding.injective _)

noncomputable def privateAlphabetDecoder {Y : Type*} [Fintype Y] [Nonempty Y]
    (a : ℕ) (ha : 0 < a) (hcard : Fintype.card Y ≤ 2 ^ a) :
    (Fin (36 * a) → Bool) → Y :=
  finiteDecode a hcard ∘ BinaryCode.privateDecoder a ha

theorem privateAlphabetDecoder_surjective {Y : Type*} [Fintype Y] [Nonempty Y]
    (a : ℕ) (ha : 0 < a) (hcard : Fintype.card Y ≤ 2 ^ a) :
    Function.Surjective (privateAlphabetDecoder a ha hcard) :=
  (finiteDecode_surjective a hcard).comp (BinaryCode.privateDecoder_surjective a ha)

end FiniteEncoding

end
