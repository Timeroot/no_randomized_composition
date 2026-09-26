import QueryComplexity.BernoulliProduct
import QueryComplexity.BernoulliSmoothing
import Mathlib.Data.Finset.Powerset

namespace QueryComplexity.BoolCounting

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

def trueSet (x : I → Bool) : Finset I := Finset.univ.filter (fun i => x i = true)

def ofSet (s : Finset I) : I → Bool := fun i => decide (i ∈ s)

@[simp] theorem trueSet_ofSet (s : Finset I) : trueSet (ofSet s) = s := by
  ext i
  simp [trueSet, ofSet]

@[simp] theorem ofSet_trueSet (x : I → Bool) : ofSet (trueSet x) = x := by
  funext i
  simp [ofSet, trueSet]

def levelEquiv (k : ℕ) :
    {x : I → Bool // (trueSet x).card = k} ≃
      {s : Finset I // s ∈ Finset.univ.powersetCard k} where
  toFun x := ⟨trueSet x.1, by simp [x.2]⟩
  invFun s := ⟨ofSet s.1, by
    rw [trueSet_ofSet]
    exact (Finset.mem_powersetCard.mp s.2).2⟩
  left_inv x := by ext; simp
  right_inv s := by ext; simp

theorem level_card (k : ℕ) :
    Fintype.card {x : I → Bool // (trueSet x).card = k} = (Fintype.card I).choose k := by
  have h := Fintype.card_congr (levelEquiv (I := I) k)
  simpa using h

omit [DecidableEq I] in
theorem count_eq_card (x : I → Bool) :
    BernoulliProduct.count x = ((trueSet x).card : ℝ) := by
  simp only [BernoulliProduct.count, trueSet, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> rfl

theorem fair_count_mass (k : ℕ) :
    (∑ x : I → Bool, if (trueSet x).card = k then
      (1 : ℝ) / 2 ^ Fintype.card I else 0) =
      BernoulliSmoothing.fairBinomialMass (Fintype.card I) k := by
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter (fun x : I → Bool => (trueSet x).card = k)).card =
      (Fintype.card I).choose k := by
    simpa only [Fintype.card_subtype] using level_card (I := I) k
  rw [hcard]
  simp [BernoulliSmoothing.fairBinomialMass, div_eq_mul_inv]

theorem fair_count_mass_int (k : ℤ) :
    (∑ x : I → Bool, if ((trueSet x).card : ℤ) = k then
      (1 : ℝ) / 2 ^ Fintype.card I else 0) =
      BernoulliSmoothing.fairBinomialMassInt (Fintype.card I) k := by
  by_cases hk : 0 ≤ k
  · rw [BernoulliSmoothing.fairBinomialMassInt, if_pos hk]
    have heq : ∀ x : I → Bool, (((trueSet x).card : ℤ) = k) ↔ (trueSet x).card = k.toNat := by
      intro x
      omega
    simp_rw [heq]
    exact fair_count_mass k.toNat
  · rw [BernoulliSmoothing.fairBinomialMassInt, if_neg hk]
    apply Finset.sum_eq_zero
    intro x _
    rw [if_neg (by omega)]

end QueryComplexity.BoolCounting
