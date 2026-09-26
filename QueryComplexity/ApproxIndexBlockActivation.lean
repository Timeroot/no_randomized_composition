import QueryComplexity.ApproxIndexActivation
import QueryComplexity.FiniteAveraging

/-! Averaging the local activation bound over independently sampled addresses. -/

open scoped BigOperators

namespace QueryComplexity.ApproxIndex

open FiniteProbability DecisionTree

variable {k : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

def encodeBlocks (radius : ℕ) (a : I → Fin k → Bool) (z : I → Bool) :
    I × ApproxIndexCoordinates k → Bool := fun p => encode radius (a p.1) (z p.1) p.2

def projectAddressTree (radius : ℕ)
    (tree : DecisionTree (I × ApproxIndexCoordinates k) Bool)
    (a : I → Fin k → Bool) (z : I → Bool) (i : I) :
    DecisionTree (ApproxIndexCoordinates k) Bool := tree.projectBlock i (encodeBlocks radius a z)

theorem encodeBlocks_update (radius : ℕ) (a : I → Fin k → Bool) (z : I → Bool)
    (i : I) (b : Fin k → Bool) :
    encodeBlocks radius (Function.update a i b) z =
      replaceBlock i (encodeBlocks radius a z) (encode radius b (z i)) := by
  funext p
  rcases p with ⟨j, coord⟩
  by_cases hj : j = i
  · subst j
    simp [encodeBlocks, replaceBlock]
  · simp [encodeBlocks, replaceBlock, hj]

theorem projectAddressTree_update (radius : ℕ)
    (tree : DecisionTree (I × ApproxIndexCoordinates k) Bool)
    (a : I → Fin k → Bool) (z : I → Bool) (i : I) (b : Fin k → Bool) :
    projectAddressTree radius tree (Function.update a i b) z i =
      projectAddressTree radius tree a z i := by
  unfold projectAddressTree projectBlock
  congr 1
  funext p
  rcases p with ⟨j, coord⟩
  by_cases hj : j = i
  · subst j
    simp [blockSubstitution]
  · simp [blockSubstitution, encodeBlocks, hj]

noncomputable def blockActivated (radius : ℕ)
    (tree : DecisionTree (I × ApproxIndexCoordinates k) Bool)
    (a : I → Fin k → Bool) (z : I → Bool) (i : I) : ℝ :=
  if hitsBall radius (projectAddressTree radius tree a z i) (a i) then 1 else 0

theorem blockActivation_resample_le (radius budget : ℕ) (η : ℝ)
    (hbudget : 0 < budget) (hη : 0 ≤ η) (hball : @BallSliceBound k radius budget η)
    (tree : DecisionTree (I × ApproxIndexCoordinates k) Bool)
    (a : I → Fin k → Bool) (z : I → Bool) (i : I) :
    average (fun b => blockActivated radius tree (Function.update a i b) z i) ≤
      average (fun b => (tree.blockCost i (encodeBlocks radius (Function.update a i b) z) : ℝ)) /
        (budget : ℝ) + (budget : ℝ) * η := by
  simp only [blockActivated, projectAddressTree_update, Function.update_self]
  have h := activationProbability_le_expectedCost radius budget η hbudget hη hball
    (projectAddressTree radius tree a z i) (z i)
  simpa only [average, activationProbability, seedExpectedCost, projectAddressTree,
    cost_projectBlock, encodeBlocks_update] using h

theorem blockActivation_average_le (radius budget : ℕ) (η : ℝ)
    (hbudget : 0 < budget) (hη : 0 ≤ η) (hball : @BallSliceBound k radius budget η)
    (tree : DecisionTree (I × ApproxIndexCoordinates k) Bool) (z : I → Bool) (i : I) :
    average (fun a => blockActivated radius tree a z i) ≤
      average (fun a => (tree.blockCost i (encodeBlocks radius a z) : ℝ)) / (budget : ℝ) +
        (budget : ℝ) * η := by
  have h := average_le (fun a => blockActivation_resample_le radius budget η
    hbudget hη hball tree a z i)
  simp only [average_add, average_div, average_const] at h
  rw [average_resample i (fun a => blockActivated radius tree a z i),
    average_resample i (fun a => (tree.blockCost i (encodeBlocks radius a z) : ℝ))] at h
  exact h

/-- The expected number of activated seed blocks is controlled by the total
query budget, even when queries switch adaptively among all blocks. -/
theorem expected_activated_blocks_le (radius budget q : ℕ) (η : ℝ)
    (hbudget : 0 < budget) (hη : 0 ≤ η) (hball : @BallSliceBound k radius budget η)
    (tree : DecisionTree (I × ApproxIndexCoordinates k) Bool) (z : I → Bool)
    (hdepth : tree.depth ≤ q) :
    average (fun a => ∑ i, blockActivated radius tree a z i) ≤
      (q : ℝ) / (budget : ℝ) + (Fintype.card I : ℝ) * ((budget : ℝ) * η) := by
  have hcost : average (fun a => ∑ i, (tree.blockCost i (encodeBlocks radius a z) : ℝ)) ≤ q := by
    calc
      _ ≤ average (fun _ : I → Fin k → Bool => (q : ℝ)) := average_le fun a => by
        rw [← Nat.cast_sum, sum_blockCost]
        exact_mod_cast (queryCost_le_depth tree (encodeBlocks radius a z)).trans hdepth
      _ = _ := average_const _
  rw [average_sum]
  calc
    _ ≤ ∑ i, (average (fun a => (tree.blockCost i (encodeBlocks radius a z) : ℝ)) /
        (budget : ℝ) + (budget : ℝ) * η) := Finset.sum_le_sum fun i _ =>
      blockActivation_average_le radius budget η hbudget hη hball tree z i
    _ = average (fun a => ∑ i, (tree.blockCost i (encodeBlocks radius a z) : ℝ)) /
        (budget : ℝ) + (Fintype.card I : ℝ) * ((budget : ℝ) * η) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← average_sum]
      simp
    _ ≤ _ := add_le_add (div_le_div_of_nonneg_right hcost (Nat.cast_nonneg _)) (le_refl _)

end QueryComplexity.ApproxIndex
