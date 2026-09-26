import QueryComplexity.Algorithms.RobustOr
import QueryComplexity.CheatSheet.Basic

/-! Robust AND and AND-of-ORs algorithms, including their short-circuit certificate interface. -/

namespace QueryComplexity.RobustAnd

variable {Seed T : Type*} [Fintype Seed] {m : ℕ}

/-- The dual fixed-cap AND algorithm. -/
noncomputable def robust (oracle : RandomizedOracle Seed (Fin m) T) :
    FiniteRandomizedTree (RandomizedOracle.Seeds Seed (3000 * m + 1)) T Bool :=
  (RobustOr.robust oracle.flipped).mapOutput Bool.not

theorem robust_depthBound (oracle : RandomizedOracle Seed (Fin m) T) (hm : 0 < m)
    {cost : ℕ} (hcost : ∀ query seed, (oracle.tree query seed).depth ≤ cost) :
    (robust oracle).DepthBound (3001 * m * cost) := by
  apply (FiniteRandomizedTree.depthBound_mapOutput _ _ _).2
  apply RobustOr.robust_depthBound oracle.flipped hm
  intro query seed
  simpa [RandomizedOracle.flipped] using hcost query seed

/-- All true-biased components force AND to be true. -/
theorem robust_one (oracle : RandomizedOracle Seed (Fin m) T) (hm : 0 < m) (x : T → Bool)
    (hone : ∀ i, 2 / 3 ≤ oracle.acceptProbability x i) :
    (robust oracle).probability (fun b => b = false) x ≤ 1 / 100 := by
  unfold robust
  rw [FiniteRandomizedTree.probability_map_not_false]
  apply RobustOr.robust_zero oracle.flipped hm x
  intro i
  rw [RandomizedOracle.acceptProbability_flipped]
  linarith [hone i]

/-- One false-biased component forces AND to be false, with no restriction
on the other component biases. -/
theorem robust_zero (oracle : RandomizedOracle Seed (Fin m) T) (hm : 0 < m) (x : T → Bool)
    (bad : Fin m) (hbad : oracle.acceptProbability x bad ≤ 1 / 3) :
    (robust oracle).probability (fun b => b = true) x ≤ 1 / 100 := by
  unfold robust
  rw [FiniteRandomizedTree.probability_map_not_true]
  apply RobustOr.robust_one oracle.flipped hm x bad
  rw [RandomizedOracle.acceptProbability_flipped]
  linarith

end QueryComplexity.RobustAnd

namespace QueryComplexity.RobustAndOr

variable {Seed T : Type*} [Fintype Seed] {m : ℕ}

def rowFamily (oracle : RandomizedOracle Seed (Fin m × Fin m) T) (row : Fin m) :
    RandomizedOracle Seed (Fin m) T := oracle.queryMap (fun col => (row, col))

/-- Each row call uses independent randomness for its complete robust OR. -/
noncomputable def rowOracle (oracle : RandomizedOracle Seed (Fin m × Fin m) T) :
    RandomizedOracle (RandomizedOracle.Seeds Seed (3000 * m + 1)) (Fin m) T where
  weight := oracle.seedsWeight (3000 * m + 1)
  weight_nonneg := oracle.seedsWeight_nonneg _
  weight_sum := oracle.seedsWeight_sum _
  tree row := (RobustOr.robust (rowFamily oracle row)).tree

theorem rowOracle_call (oracle : RandomizedOracle Seed (Fin m × Fin m) T) (row : Fin m) :
    (rowOracle oracle).call row = RobustOr.robust (rowFamily oracle row) := by
  cases oracle
  simp only [rowOracle, RandomizedOracle.call, RobustOr.robust, RobustOr.algorithm,
    RandomizedOracle.algorithm, rowFamily]
  congr 1
  funext seed
  exact (RandomizedOracle.seedsWeight_queryMap _ _ _ seed).symm

noncomputable def robust (oracle : RandomizedOracle Seed (Fin m × Fin m) T) :
    FiniteRandomizedTree
      (RandomizedOracle.Seeds (RandomizedOracle.Seeds Seed (3000 * m + 1)) (3000 * m + 1)) T Bool :=
  RobustAnd.robust (rowOracle oracle)

theorem robust_depthBound (oracle : RandomizedOracle Seed (Fin m × Fin m) T) (hm : 0 < m)
    {cost : ℕ} (hcost : ∀ query seed, (oracle.tree query seed).depth ≤ cost) :
    (robust oracle).DepthBound (3001 ^ 2 * m ^ 2 * cost) := by
  have hrow : ∀ row seed, ((rowOracle oracle).tree row seed).depth ≤ 3001 * m * cost := by
    intro row seed
    exact RobustOr.robust_depthBound (rowFamily oracle row) hm
      (fun col seed => hcost (row, col) seed) seed
  have h := RobustAnd.robust_depthBound (rowOracle oracle) hm hrow
  convert h using 1
  ring

/-- A true-biased entry in every row suffices, with arbitrary remaining biases. -/
theorem robust_one (oracle : RandomizedOracle Seed (Fin m × Fin m) T) (hm : 0 < m)
    (x : T → Bool) (hone : ∀ row, ∃ col, 2 / 3 ≤ oracle.acceptProbability x (row, col)) :
    (robust oracle).probability (fun b => b = false) x ≤ 1 / 100 := by
  apply RobustAnd.robust_one (rowOracle oracle) hm x
  intro row
  obtain ⟨col, hcol⟩ := hone row
  have h := RobustOr.robust_one (rowFamily oracle row) hm x col hcol
  rw [FiniteRandomizedTree.probability_false] at h
  rw [RandomizedOracle.acceptProbability, rowOracle_call]
  grind

/-- One row of false-biased entries suffices, with arbitrary remaining biases. -/
theorem robust_zero (oracle : RandomizedOracle Seed (Fin m × Fin m) T) (hm : 0 < m)
    (x : T → Bool) (hzero : ∃ row, ∀ col, oracle.acceptProbability x (row, col) ≤ 1 / 3) :
    (robust oracle).probability (fun b => b = true) x ≤ 1 / 100 := by
  obtain ⟨row, hrow⟩ := hzero
  apply RobustAnd.robust_zero (rowOracle oracle) hm x row
  rw [RandomizedOracle.acceptProbability, rowOracle_call]
  exact (RobustOr.robust_zero (rowFamily oracle row) hm x hrow).trans (by norm_num)

end QueryComplexity.RobustAndOr

namespace QueryComplexity.KleeneAlgorithms

variable {Seed S U : Type*} [Fintype Seed] {m : ℕ}

def oracle (seedAlgorithm : FiniteRandomizedTree Seed (S × U) Bool) :
    RandomizedOracle Seed (Fin m × Fin m) (((Fin m × Fin m) × S) × U) :=
  RandomizedOracle.ofSubstitutions seedAlgorithm
    (fun pair coordinate => .inr (((pair, coordinate.1), coordinate.2), id))

theorem oracle_probability (seedAlgorithm : FiniteRandomizedTree Seed (S × U) Bool)
    (x : ((Fin m × Fin m) × S) × U → Bool) (pair : Fin m × Fin m) (event : Bool → Prop) :
    ((oracle seedAlgorithm).call pair).probability event x =
      seedAlgorithm.probability event (fun coordinate => x ((pair, coordinate.1), coordinate.2)) := by
  simp only [oracle, RandomizedOracle.call_ofSubstitutions,
    FiniteRandomizedTree.probability_substitute]
  rfl

noncomputable def algorithm (seedAlgorithm : FiniteRandomizedTree Seed (S × U) Bool) :
    FiniteRandomizedTree
      (RandomizedOracle.Seeds (RandomizedOracle.Seeds Seed (3000 * m + 1)) (3000 * m + 1))
      (((Fin m × Fin m) × S) × U) Bool :=
  RobustAndOr.robust (oracle seedAlgorithm)

theorem algorithm_depthBound (seedAlgorithm : FiniteRandomizedTree Seed (S × U) Bool)
    (hm : 0 < m) {cost : ℕ} (hcost : seedAlgorithm.DepthBound cost) :
    (algorithm (m := m) seedAlgorithm).DepthBound (3001 ^ 2 * m ^ 2 * cost) := by
  apply RobustAndOr.robust_depthBound _ hm
  intro pair seed
  exact (DecisionTree.depth_substitute_le _ _).trans (hcost seed)

theorem algorithm_error (p : (S → Bool) → Option Bool) (g : BoolFn U)
    (seedAlgorithm : FiniteRandomizedTree Seed (S × U) Bool) (hm : 0 < m)
    (hseed : ∀ input b, p (fun s => g (fun u => input (s, u))) = some b →
      seedAlgorithm.probability (fun output => output ≠ b) input ≤ 1 / 3)
    (x : ((Fin m × Fin m) × S) × U → Bool) (b : Bool)
    (hw : ∃ w, kleeneValid p (fun row col s => g (fun u => x (((row, col), s), u))) b w) :
    (algorithm seedAlgorithm).probability (fun output => output ≠ b) x ≤ 1 / 100 := by
  obtain ⟨w, hw⟩ := hw
  cases b with
  | false =>
      cases w with
      | inl select => exact False.elim hw
      | inr row =>
          have h := RobustAndOr.robust_zero (oracle seedAlgorithm) hm x (by
            refine ⟨row, fun col => ?_⟩
            rw [RandomizedOracle.acceptProbability, oracle_probability]
            have he := hseed (fun coordinate => x (((row, col), coordinate.1), coordinate.2)) false (hw col)
            simpa only [Bool.not_eq_false] using he)
          simpa only [Bool.not_eq_false] using h
  | true =>
      cases w with
      | inr row => exact False.elim hw
      | inl select =>
          have h := RobustAndOr.robust_one (oracle seedAlgorithm) hm x (by
            intro row
            refine ⟨select row, ?_⟩
            rw [RandomizedOracle.acceptProbability, oracle_probability]
            have he := hseed (fun coordinate => x (((row, select row), coordinate.1), coordinate.2)) true (hw row)
            simp only [Bool.not_eq_true] at he
            rw [FiniteRandomizedTree.probability_false] at he
            linarith)
          simpa only [Bool.not_eq_true] using h

end QueryComplexity.KleeneAlgorithms
