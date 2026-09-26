import QueryComplexity.Algorithms
import QueryComplexity.ApproxIndex

namespace QueryComplexity.ApproxIndex

/-- Read the address and then the addressed value bit. -/
noncomputable def exactTree (k : ℕ) : DecisionTree (ApproxIndexCoordinates k) Bool :=
  (DecisionTree.readCoordinates (fun i : Fin k => (Sum.inl i : ApproxIndexCoordinates k))).bind
    (fun a => DecisionTree.query (.inr (a, true)))

@[simp] theorem exactTree_eval (k : ℕ) (x : ApproxIndexCoordinates k → Bool) :
    (exactTree k).eval x = extension x := by
  simp only [exactTree, DecisionTree.eval_bind, DecisionTree.eval_readCoordinates,
    DecisionTree.eval_query]
  rfl

theorem exactTree_depth_le (k : ℕ) : (exactTree k).depth ≤ k + 1 := by
  apply DecisionTree.depth_bind_le_add
  · simpa using DecisionTree.depth_readCoordinates_le
      (fun i : Fin k => (Sum.inl i : ApproxIndexCoordinates k))
  · intro a
    simp

theorem hasRandomizedBound_extension (k : ℕ) :
    HasRandomizedBound (@extension k) (k + 1) :=
  hasRandomizedBound_of_tree (exactTree k) (exactTree_eval k) (exactTree_depth_le k)

theorem R_extension_le (k : ℕ) : R (@extension k) ≤ k + 1 :=
  R_le_of_hasRandomizedBound (hasRandomizedBound_extension k)

theorem exactTree_correct {k radius : ℕ} {x : ApproxIndexCoordinates k → Bool} {z : Bool}
    (h : value radius x = some z) : (exactTree k).eval x = z := by
  rw [exactTree_eval]
  exact extension_correct radius x z h

end QueryComplexity.ApproxIndex
