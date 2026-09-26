import QueryComplexity.CodeExistence
import QueryComplexity.Certificates
import QueryComplexity.Pointer
import Mathlib.Data.Fintype.EquivFin

namespace QueryComplexity

/-- Decode enough bits onto an arbitrary nonempty finite alphabet. This is
an ordinary total map; the selected embedding has no computational cost in
the query model. -/
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

def pointerCellEquiv (q : ℕ) :
    PointerCell q ≃ Bool × (Fin q → Option (Fin q)) × Option (Fin q) where
  toFun c := (c.bit, c.row, c.col)
  invFun c := ⟨c.1, c.2.1, c.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance pointerCellNonempty (q : ℕ) : Nonempty (PointerCell q) :=
  ⟨⟨false, fun _ => none, none⟩⟩

theorem pointerCell_card_bound (q : ℕ) :
    Fintype.card (PointerCell q) ≤ 2 ^ (1 + q * (q + 1)) := by
  rw [Fintype.card_congr (pointerCellEquiv q)]
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fun,
    Fintype.card_option, Fintype.card_fin]
  have hq : q + 1 ≤ 2 ^ q := Nat.succ_le_of_lt Nat.lt_two_pow_self
  calc
    2 * ((q + 1) ^ q * (q + 1)) ≤ 2 * ((2 ^ q) ^ q * 2 ^ q) := by gcongr
    _ = 2 ^ (1 + q * (q + 1)) := by
      rw [pow_add, pow_mul, pow_one, pow_succ]

instance kleeneWitnessNonempty (m : ℕ) : Nonempty (KleeneWitness (Fin m) (Fin m)) :=
  ⟨.inl id⟩

theorem kleeneWitness_card_bound (m : ℕ) :
    Fintype.card (KleeneWitness (Fin m) (Fin m)) ≤ 2 ^ (m * m + 1) := by
  simp only [KleeneWitness, Fintype.card_sum, Fintype.card_fun, Fintype.card_fin]
  have hm : m ≤ 2 ^ m := Nat.lt_two_pow_self.le
  have hpow : m ^ m ≤ 2 ^ (m * m) := by simpa [pow_mul] using Nat.pow_le_pow_left hm m
  have hsmall : m ≤ 2 ^ (m * m) := by
    cases m with
    | zero => simp
    | succ m =>
      exact hm.trans (Nat.pow_le_pow_right (by omega) (by nlinarith))
  rw [pow_succ]
  omega

theorem certificatePayload_card_bound (m c : ℕ) :
    Fintype.card (Bool × (Fin c → KleeneWitness (Fin m) (Fin m))) ≤
      2 ^ (1 + c * (m * m + 1)) := by
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fun, Fintype.card_fin]
  calc
    2 * Fintype.card (KleeneWitness (Fin m) (Fin m)) ^ c ≤
        2 * (2 ^ (m * m + 1)) ^ c := by
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (kleeneWitness_card_bound m) c)
    _ = _ := by
      rw [← pow_mul, mul_comm (m * m + 1) c, pow_add]
      simp

end QueryComplexity
