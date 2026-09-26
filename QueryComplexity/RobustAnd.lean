import QueryComplexity.RobustOr

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
