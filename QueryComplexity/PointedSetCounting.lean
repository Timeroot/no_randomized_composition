import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace QueryComplexity.PointedSetCounting

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev PointedChoice (I : Type*) [Fintype I] (k : ℕ) :=
  {choice : Finset I × I // choice.2 ∈ choice.1 ∧ choice.1.card = k}

def choiceEquiv (k : ℕ) :
    PointedChoice I k ≃ Σ s : {s : Finset I // s ∈ Finset.univ.powersetCard k}, s.1 where
  toFun c := ⟨⟨c.1.1, by simp [c.2.2]⟩, ⟨c.1.2, c.2.1⟩⟩
  invFun s := ⟨(s.1.1, s.2.1), s.2.2, (Finset.mem_powersetCard.mp s.1.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem choice_card (k : ℕ) :
    Fintype.card (PointedChoice I k) = (Fintype.card I).choose k * k := by
  classical
  rw [Fintype.card_congr (choiceEquiv (I := I) k), Fintype.card_sigma]
  have heq : ∀ s : {s : Finset I // s ∈ Finset.univ.powersetCard k},
      Fintype.card s.1 = k := by
    intro s
    simpa using (Finset.mem_powersetCard.mp s.2).2
  simp_rw [heq]
  simp

noncomputable def avoidChoiceEquiv (D : Finset I) (k : ℕ) :
    {c : PointedChoice I k // Disjoint c.1.1 D} ≃
      Σ s : {s : Finset I // s ∈ Dᶜ.powersetCard k}, s.1 where
  toFun c := ⟨⟨c.1.1.1, Finset.mem_powersetCard.mpr ⟨by
    intro i hi
    exact Finset.mem_compl.mpr (fun hD => Finset.disjoint_left.mp c.2 hi hD), c.1.2.2⟩⟩,
    ⟨c.1.1.2, c.1.2.1⟩⟩
  invFun s := ⟨⟨(s.1.1, s.2.1), s.2.2, (Finset.mem_powersetCard.mp s.1.2).2⟩, by
    apply Finset.disjoint_left.mpr
    intro i hi hD
    exact Finset.mem_compl.mp ((Finset.mem_powersetCard.mp s.1.2).1 hi) hD⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem avoid_choice_card (D : Finset I) (k : ℕ) :
    Fintype.card {c : PointedChoice I k // Disjoint c.1.1 D} =
      (Fintype.card I - D.card).choose k * k := by
  classical
  rw [Fintype.card_congr (avoidChoiceEquiv D k), Fintype.card_sigma]
  have heq : ∀ s : {s : Finset I // s ∈ Dᶜ.powersetCard k}, Fintype.card s.1 = k := by
    intro s
    simpa using (Finset.mem_powersetCard.mp s.2).2
  simp_rw [heq]
  simp [Finset.card_compl]

theorem avoidance_probability (D : Finset I) (k : ℕ) (hk : 0 < k) :
    (Fintype.card {c : PointedChoice I k // Disjoint c.1.1 D} : ℝ) /
        (Fintype.card (PointedChoice I k) : ℝ) =
      ((Fintype.card I - D.card).choose k : ℝ) / ((Fintype.card I).choose k : ℝ) := by
  rw [avoid_choice_card, choice_card]
  push_cast
  exact mul_div_mul_right _ _ (by exact_mod_cast hk.ne' : (k : ℝ) ≠ 0)

end QueryComplexity.PointedSetCounting
