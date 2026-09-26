import QueryComplexity.PointerLayers
import QueryComplexity.CodedRLower
import QueryComplexity.Families

open scoped BigOperators

namespace QueryComplexity.PointerDistributions

open FiniteProbability Construction CodedOracleSimulation

abbrev FlatCoordinates (q : ℕ) := Fin q × (Fin q × Fin q)

def blockCellEquiv (q : ℕ) : BlockInput q ≃ (FlatCoordinates q → PointerCell q) where
  toFun x p := x p.1 p.2.1 p.2.2
  invFun s i row col := s (i, (row, col))
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def flatMajority (q : ℕ) (s : FlatCoordinates q → PointerCell q) : Bool :=
  cellMajority q ((blockCellEquiv q).symm s)

noncomputable def flatHardWeight (m : ℕ) : Weight (FlatCoordinates (2 * m + 1) → PointerCell (2 * m + 1)) :=
  pushforward (majorityHardWeight m) (blockCellEquiv (2 * m + 1))

theorem flatHardWeight_nonnegative (m : ℕ) : Nonnegative (flatHardWeight m) :=
  pushforward_nonnegative (majorityHardWeight_nonnegative m) _

theorem flatHardWeight_mass (m : ℕ) : mass (flatHardWeight m) = 1 := by
  rw [flatHardWeight, mass_pushforward, majorityHardWeight_mass]

theorem flatHardWeight_score (m : ℕ)
    (tree : OracleTree (FlatCoordinates (2 * m + 1)) (PointerCell (2 * m + 1)) Bool) :
    OracleOptimization.score (flatMajority (2 * m + 1)) (flatHardWeight m) tree =
      ∑ x : BlockInput (2 * m + 1),
        if tree.eval (blockCellEquiv (2 * m + 1) x) = cellMajority (2 * m + 1) x
          then majorityHardWeight m x else 0 := by
  classical
  have h := sum_pushforward_mul (majorityHardWeight m) (blockCellEquiv (2 * m + 1))
    (fun s => if tree.eval s = flatMajority (2 * m + 1) s then (1 : ℝ) else 0)
  simpa only [OracleOptimization.score, flatHardWeight, flatMajority, Equiv.symm_apply_apply,
    mul_ite, mul_one, mul_zero] using h

def encodedCoordinatesEquiv (q a : ℕ) :
    FlatCoordinates q × Fin (36 * a) ≃ Fin q × ((Fin q × Fin q) × Fin (36 * a)) :=
  Equiv.prodAssoc _ _ _

theorem inner_eq_reindex (q : ℕ) :
    inner q = reindex (encodedCoordinatesEquiv q (pointerPayloadWidth q))
      (blockEncoded (flatMajority q) (pointerDecoder q)) := rfl

/-- Any distributional lower bound against full pointer-cell queries lifts
to the concrete total Boolean inner function, with the proved coding factor. -/
theorem R_inner_lower_of_cell_bound (m B : ℕ) (β : ℝ) (hβ : β < 2 / 3)
    (hhard : ∀ tree : OracleTree (FlatCoordinates (2 * m + 1)) (PointerCell (2 * m + 1)) Bool,
      tree.depth ≤ B →
      (∑ x : BlockInput (2 * m + 1),
        if tree.eval (blockCellEquiv (2 * m + 1) x) = cellMajority (2 * m + 1) x
          then majorityHardWeight m x else 0) ≤ β) :
    (B + 1) * (12 * pointerPayloadWidth (2 * m + 1) + 1) ≤ R (inner (2 * m + 1)) := by
  classical
  let q := 2 * m + 1
  let a := pointerPayloadWidth q
  have ha : 0 < a := by dsimp [a, pointerPayloadWidth]; omega
  let D : (Fin a → Bool) → PointerCell q := finiteDecode a (pointerCell_card_bound q)
  choose payload hpayload using finiteDecode_surjective a (pointerCell_card_bound q)
  have h := R_blockEncoded_lower (flatMajority q) a ha D payload hpayload B
    (flatHardWeight m) (flatHardWeight_nonnegative m) (flatHardWeight_mass m) β hβ (by
      intro tree ht
      rw [flatHardWeight_score]
      exact hhard tree ht)
  rw [inner_eq_reindex, R_reindex]
  exact h

end QueryComplexity.PointerDistributions
