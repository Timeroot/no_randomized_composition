import QueryComplexity.ApproxIndex.Lower
import QueryComplexity.DecisionTree.Cost

/-! Expected query cost of activating one approximate-index block. -/

open scoped BigOperators

namespace QueryComplexity.ApproxIndex

open FiniteProbability DecisionTree

variable {k : ℕ}

theorem hitsBall_truncate_of_cost_lt (radius budget : ℕ)
    (tree : DecisionTree (ApproxIndexCoordinates k) Bool) (a : Fin k → Bool) (z : Bool)
    (hcost : tree.queryCost (encode radius a z) < budget) (hhit : hitsBall radius tree a) :
    hitsBall radius (tree.truncate false budget) a := by
  induction budget generalizing tree with
  | zero => omega
  | succ budget ih =>
    cases tree with
    | leaf answer => exact hhit.elim
    | node coordinate zero one =>
      cases coordinate with
      | inl i =>
        by_cases hx : a i = true
        · simp only [hitsBall, hx, if_true] at hhit
          simp only [queryCost, encode, hx, if_true] at hcost
          simp only [truncate, hitsBall, hx, if_true]
          exact ih one (by omega) hhit
        · have hf : a i = false := Bool.eq_false_of_not_eq_true hx
          simp only [hitsBall, hf, Bool.false_eq_true, if_false] at hhit
          simp only [queryCost, encode, hf, Bool.false_eq_true, if_false] at hcost
          simp only [truncate, hitsBall, hf, Bool.false_eq_true, if_false]
          exact ih zero (by omega) hhit
      | inr p =>
        rcases p with ⟨b, bit⟩
        by_cases hb : distance a b ≤ radius
        · exact Or.inl hb
        · have hz : hitsBall radius zero a := hhit.resolve_left hb
          have hc : zero.queryCost (encode radius a z) < budget := by
            cases bit <;> simp [queryCost, encode, hb] at hcost <;> omega
          exact Or.inr (ih zero hc hz)

theorem activation_indicator_le (radius budget : ℕ)
    (tree : DecisionTree (ApproxIndexCoordinates k) Bool) (a : Fin k → Bool) (z : Bool) :
    (budget : ℝ) * (if hitsBall radius tree a then 1 else 0) ≤
      (tree.queryCost (encode radius a z) : ℝ) +
        (budget : ℝ) * (if hitsBall radius (tree.truncate false budget) a then 1 else 0) := by
  have hc0 : (0 : ℝ) ≤ tree.queryCost (encode radius a z) := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ budget := Nat.cast_nonneg _
  by_cases hh : hitsBall radius tree a
  · simp only [hh, if_true, mul_one]
    by_cases hc : budget ≤ tree.queryCost (encode radius a z)
    · have hc' : (budget : ℝ) ≤ tree.queryCost (encode radius a z) := by exact_mod_cast hc
      split_ifs <;> linarith
    · have ht := hitsBall_truncate_of_cost_lt radius budget tree a z (Nat.lt_of_not_ge hc) hh
      simp only [ht, if_true, mul_one]
      linarith
  · simp only [hh, if_false, mul_zero]
    split_ifs <;> linarith

noncomputable def activationProbability (radius : ℕ)
    (tree : DecisionTree (ApproxIndexCoordinates k) Bool) : ℝ :=
  ∑ a, uniformWeight (Fin k → Bool) a * (if hitsBall radius tree a then 1 else 0)

noncomputable def seedExpectedCost (radius : ℕ)
    (tree : DecisionTree (ApproxIndexCoordinates k) Bool) (z : Bool) : ℝ :=
  ∑ a, uniformWeight (Fin k → Bool) a * (tree.queryCost (encode radius a z) : ℝ)

theorem activationProbability_eq (radius : ℕ)
    (tree : DecisionTree (ApproxIndexCoordinates k) Bool) :
    activationProbability radius tree = hitMass radius tree [] / (2 : ℝ) ^ k := by
  simp only [activationProbability, uniformWeight, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, hitMass, sliceWeight_nil, div_eq_mul_inv]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp

theorem activationProbability_le (radius budget : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (hball : @BallSliceBound k radius budget η)
    (tree : DecisionTree (ApproxIndexCoordinates k) Bool) (hdepth : tree.depth ≤ budget) :
    activationProbability radius tree ≤ (budget : ℝ) * η := by
  rw [activationProbability_eq]
  have hh := hitMass_le radius budget η hη hball tree [] (by simpa using hdepth)
  have hm : mass (sliceWeight ([] : AddressTrace k)) = (2 : ℝ) ^ k := by simp [mass]
  rw [hm] at hh
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ k)).2
  refine hh.trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hdepth) hη) (by positivity)

/-- The probability that a block is ever touched in its non-erased region is
at most its expected local query cost divided by the threshold, plus the
small probability of activating before the threshold. The query tree may
have arbitrarily large depth. -/
theorem activationProbability_le_expectedCost (radius budget : ℕ) (η : ℝ)
    (hbudget : 0 < budget) (hη : 0 ≤ η) (hball : @BallSliceBound k radius budget η)
    (tree : DecisionTree (ApproxIndexCoordinates k) Bool) (z : Bool) :
    activationProbability radius tree ≤
      seedExpectedCost radius tree z / (budget : ℝ) + (budget : ℝ) * η := by
  have ht := activationProbability_le radius budget η hη hball
    (tree.truncate false budget) (depth_truncate_le false budget tree)
  have hsum : (budget : ℝ) * activationProbability radius tree ≤
      seedExpectedCost radius tree z +
        (budget : ℝ) * activationProbability radius (tree.truncate false budget) := by
    simp only [activationProbability, seedExpectedCost, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    have h := mul_le_mul_of_nonneg_left (activation_indicator_le radius budget tree a z)
      (uniformWeight_nonnegative (Fin k → Bool) a)
    nlinarith
  have hb : (0 : ℝ) < budget := by exact_mod_cast hbudget
  have hm := mul_le_mul_of_nonneg_left ht (le_of_lt hb)
  calc
    _ ≤ (seedExpectedCost radius tree z + (budget : ℝ) * ((budget : ℝ) * η)) / budget :=
      (le_div_iff₀ hb).2 (by nlinarith)
    _ = _ := by field_simp

end QueryComplexity.ApproxIndex
