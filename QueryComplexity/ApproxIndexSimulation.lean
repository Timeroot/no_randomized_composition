import QueryComplexity.ApproxIndexBlockActivation
import QueryComplexity.QueryMemoization

/-! An exact randomized simulation of a seed-composed query tree by a tree
querying the outer bits. Addresses are sampled uniformly, and caching charges
each activated outer coordinate once. -/

open scoped BigOperators

namespace QueryComplexity.ApproxIndex

open FiniteProbability DecisionTree

variable {k : ℕ}

def insideBall (radius : ℕ) (a : Fin k → Bool) : ApproxIndexCoordinates k → Prop
  | .inl _ => False
  | .inr (b, _) => distance a b ≤ radius

theorem hitsBall_iff_visited (radius : ℕ) (tree : DecisionTree (ApproxIndexCoordinates k) Bool)
    (a : Fin k → Bool) (z : Bool) :
    hitsBall radius tree a ↔
      ∃ coord ∈ tree.visited (encode radius a z), insideBall radius a coord := by
  induction tree with
  | leaf answer => simp [hitsBall, visited]
  | node coordinate zero one ihz iho =>
    cases coordinate with
    | inl i =>
      by_cases hx : a i = true
      · simp [hitsBall, visited, encode, insideBall, hx, ihz, iho, or_and_right, exists_or]
      · have hf : a i = false := Bool.eq_false_of_not_eq_true hx
        simp [hitsBall, visited, encode, insideBall, hf, ihz, iho, or_and_right, exists_or]
    | inr p =>
      rcases p with ⟨b, bit⟩
      by_cases hb : distance a b ≤ radius <;> cases bit <;>
        simp [hitsBall, visited, encode, insideBall, hb, ihz, iho, or_and_right, exists_or]

variable {I : Type*} [Fintype I] [DecidableEq I]

def seedSubstitution (radius : ℕ) (a : I → Fin k → Bool) :
    BitSubstitution I (I × ApproxIndexCoordinates k)
  | (i, .inl j) => .inl (a i j)
  | (i, .inr (b, false)) => .inl (decide (distance (a i) b ≤ radius))
  | (i, .inr (b, true)) =>
      if distance (a i) b ≤ radius then .inr (i, id) else .inl false

@[simp] theorem seedSubstitution_eval (radius : ℕ) (a : I → Fin k → Bool) (z : I → Bool) :
    (seedSubstitution radius a).eval z = encodeBlocks radius a z := by
  funext p
  rcases p with ⟨i, coord⟩
  cases coord with
  | inl j => rfl
  | inr p =>
    rcases p with ⟨b, bit⟩
    cases bit
    · rfl
    · by_cases hb : distance (a i) b ≤ radius <;>
        simp [seedSubstitution, BitSubstitution.eval, encodeBlocks, encode, hb]

def simulatedTree (radius : ℕ) (tree : DecisionTree (I × ApproxIndexCoordinates k) Bool)
    (a : I → Fin k → Bool) : DecisionTree I Bool :=
  (tree.substitute (seedSubstitution radius a)).cached

@[simp] theorem simulatedTree_eval (radius : ℕ)
    (tree : DecisionTree (I × ApproxIndexCoordinates k) Bool)
    (a : I → Fin k → Bool) (z : I → Bool) :
    (simulatedTree radius tree a).eval z = tree.eval (encodeBlocks radius a z) := by
  simp [simulatedTree]

theorem visited_simulation_imp_activated (radius : ℕ)
    (tree : DecisionTree (I × ApproxIndexCoordinates k) Bool)
    (a : I → Fin k → Bool) (z : I → Bool) (i : I)
    (hi : i ∈ (tree.substitute (seedSubstitution radius a)).visited z) :
    hitsBall radius (projectAddressTree radius tree a z i) (a i) := by
  rw [mem_visited_substitute, seedSubstitution_eval] at hi
  rcases hi with ⟨⟨j, coord⟩, hvisited, value, hmap⟩
  cases coord with
  | inl l => simp [seedSubstitution] at hmap
  | inr p =>
    rcases p with ⟨b, bit⟩
    cases bit
    · simp [seedSubstitution] at hmap
    · by_cases hb : distance (a j) b ≤ radius
      · simp only [seedSubstitution, hb, if_true] at hmap
        have hj : j = i := congrArg Prod.fst (Sum.inr.inj hmap)
        subst j
        apply (hitsBall_iff_visited radius _ (a i) (z i)).2
        refine ⟨.inr (b, true), ?_, hb⟩
        unfold projectAddressTree
        apply (mem_visited_projectBlock tree i (encodeBlocks radius a z)
          (encode radius (a i) (z i)) (.inr (b, true))).2
        have he : replaceBlock i (encodeBlocks radius a z) (encode radius (a i) (z i)) =
            encodeBlocks radius a z := replaceBlock_self i (encodeBlocks radius a z)
        simpa only [he] using hvisited
      · simp [seedSubstitution, hb] at hmap

theorem simulatedTree_cost_le_activations (radius : ℕ)
    (tree : DecisionTree (I × ApproxIndexCoordinates k) Bool)
    (a : I → Fin k → Bool) (z : I → Bool) :
    ((simulatedTree radius tree a).queryCost z : ℝ) ≤
      ∑ i, blockActivated radius tree a z i := by
  classical
  have hsub : (tree.substitute (seedSubstitution radius a)).visited z ⊆
      Finset.univ.filter (fun i => hitsBall radius (projectAddressTree radius tree a z i) (a i)) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
      visited_simulation_imp_activated radius tree a z i hi⟩
  calc
    _ = (((tree.substitute (seedSubstitution radius a)).visited z).card : ℝ) := by
      simp [simulatedTree]
    _ ≤ ((Finset.univ.filter (fun i =>
        hitsBall radius (projectAddressTree radius tree a z i) (a i))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ = _ := by simp [blockActivated, Finset.sum_boole]

/-- For every outer input, the exact simulation has expected outer-query cost
at most `Q/budget + numberBlocks*budget*η`. -/
theorem simulatedTree_expected_cost_le (radius budget Q : ℕ) (η : ℝ)
    (hbudget : 0 < budget) (hη : 0 ≤ η) (hball : @BallSliceBound k radius budget η)
    (tree : DecisionTree (I × ApproxIndexCoordinates k) Bool) (z : I → Bool)
    (hdepth : tree.depth ≤ Q) :
    average (fun a => ((simulatedTree radius tree a).queryCost z : ℝ)) ≤
      (Q : ℝ) / (budget : ℝ) + (Fintype.card I : ℝ) * ((budget : ℝ) * η) := by
  calc
    _ ≤ average (fun a => ∑ i, blockActivated radius tree a z i) :=
      average_le fun a => simulatedTree_cost_le_activations radius tree a z
    _ ≤ _ := expected_activated_blocks_le radius budget Q η hbudget hη hball tree z hdepth

end QueryComplexity.ApproxIndex
