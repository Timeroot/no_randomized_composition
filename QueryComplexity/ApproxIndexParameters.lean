import QueryComplexity.ApproxIndexFourthMoment

/-! Explicit polynomial parameters for the partial approximate-index seed.
All quantitative inequalities hold for every positive integer parameter. -/

open scoped BigOperators

namespace QueryComplexity.ApproxIndex

open FiniteProbability DirectProduct

def seedSize (q : ℕ) : ℕ := 10000 * q ^ 4
def seedRadius (q : ℕ) : ℕ := 5000 * q ^ 4 - 500 * q ^ 3
def seedBudget (q : ℕ) : ℕ := 250 * q ^ 3
noncomputable def seedEta (q : ℕ) : ℝ := 16 / (16875 * (q : ℝ) ^ 4)

theorem seedRadius_sub_valid (q : ℕ) (hq : 0 < q) : 500 * q ^ 3 ≤ 5000 * q ^ 4 := by
  have hp : q ^ 3 ≤ q ^ 4 := pow_le_pow_right₀ (by omega : 1 ≤ q) (by omega : 3 ≤ 4)
  omega

theorem seed_gap (q : ℕ) (hq : 0 < q) :
    (seedSize q : ℝ) - 2 * (seedRadius q : ℝ) - (seedBudget q : ℝ) = 750 * (q : ℝ) ^ 3 := by
  unfold seedSize seedRadius seedBudget
  rw [Nat.cast_sub (seedRadius_sub_valid q hq)]
  push_cast
  ring

theorem seed_gap_pos (q : ℕ) (hq : 0 < q) :
    0 < (seedSize q : ℝ) - 2 * (seedRadius q : ℝ) - (seedBudget q : ℝ) := by
  rw [seed_gap q hq]
  have : (0 : ℝ) < q := by exact_mod_cast hq
  positivity

theorem seedEta_eq_fourth_moment (q : ℕ) (hq : 0 < q) :
    3 * (seedSize q : ℝ) ^ 2 /
      ((seedSize q : ℝ) - 2 * (seedRadius q : ℝ) - (seedBudget q : ℝ)) ^ 4 = seedEta q := by
  rw [seed_gap q hq]
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

theorem seedBudget_mul_eta_le (q : ℕ) (hq : 0 < q) :
    (seedBudget q : ℝ) * seedEta q ≤ 32 / 135 := by
  rw [seedBudget_mul_eta q hq]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 135 * q)).2
  nlinarith

/-- Explicit finite hard-distribution bound for actual query trees, with no
remaining combinatorial or concentration hypotheses. -/
theorem seed_hardness (q : ℕ) (hq : 0 < q)
    (tree : DecisionTree (ApproxIndexCoordinates (seedSize q)) Bool)
    (hdepth : tree.depth ≤ seedBudget q) :
    score extension (hardWeight (seedSize q) (seedRadius q)) tree ≤ (167 : ℝ) / 270 := by
  have h := hardWeight_score_le (seedRadius q) (seedBudget q) (seedEta q)
    (seedEta_nonnegative q) (seed_ballSliceBound q hq) tree hdepth
  have he := seedBudget_mul_eta_le q hq
  linarith

theorem seed_hardness_two_thirds (q : ℕ) (hq : 0 < q)
    (tree : DecisionTree (ApproxIndexCoordinates (seedSize q)) Bool)
    (hdepth : tree.depth ≤ seedBudget q) :
    score extension (hardWeight (seedSize q) (seedRadius q)) tree ≤ (2 : ℝ) / 3 :=
  (seed_hardness q hq tree hdepth).trans (by norm_num)

/-- In particular the total deterministic extension has standard randomized
query complexity greater than `250*q^3`, witnessed entirely on valid inputs. -/
theorem R_seed_extension_gt (q : ℕ) (hq : 0 < q) :
    seedBudget q < R (@extension (seedSize q)) := by
  exact R_gt_of_hard_distribution extension (seedBudget q)
    (hardWeight (seedSize q) (seedRadius q))
    (hardWeight_nonnegative _ _) (mass_hardWeight _ _) (167 / 270) (by norm_num)
    (seed_hardness q hq)

end QueryComplexity.ApproxIndex
