import QueryComplexity.RobustAnd

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
  change 2 / 3 ≤ ((rowOracle oracle).call row).probability (fun b => b = true) x
  rw [rowOracle_call]
  linarith

/-- One row of false-biased entries suffices, with arbitrary remaining biases. -/
theorem robust_zero (oracle : RandomizedOracle Seed (Fin m × Fin m) T) (hm : 0 < m)
    (x : T → Bool) (hzero : ∃ row, ∀ col, oracle.acceptProbability x (row, col) ≤ 1 / 3) :
    (robust oracle).probability (fun b => b = true) x ≤ 1 / 100 := by
  obtain ⟨row, hrow⟩ := hzero
  apply RobustAnd.robust_zero (rowOracle oracle) hm x row
  change ((rowOracle oracle).call row).probability (fun b => b = true) x ≤ 1 / 3
  rw [rowOracle_call]
  exact (RobustOr.robust_zero (rowFamily oracle row) hm x hrow).trans (by norm_num)

end QueryComplexity.RobustAndOr
