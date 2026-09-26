import QueryComplexity.ParallelAlgorithms
import QueryComplexity.BernoulliVariance
import QueryComplexity.ApproxIndex

open scoped BigOperators

namespace QueryComplexity.ApproxIndex

variable {Seed U : Type*} [Fintype Seed] [Fintype U] {k : ℕ}

/-- The Boolean seed input obtained by evaluating each inner block. -/
def blockValues (g : BoolFn U) (x : ApproxIndexCoordinates k × U → Bool) :
    ApproxIndexCoordinates k → Bool := fun coordinate => g (fun u => x (coordinate, u))

/-- Each address bit is estimated with fresh randomness. -/
def addressOracle (weak : FiniteRandomizedTree Seed U Bool) :
    RandomizedOracle Seed (Fin k) (ApproxIndexCoordinates k × U) :=
  RandomizedOracle.ofSubstitutions weak
    (fun i u => .inr ((.inl i, u), id))

omit [Fintype U] in
theorem addressOracle_probability (weak : FiniteRandomizedTree Seed U Bool)
    (x : ApproxIndexCoordinates k × U → Bool) (i : Fin k) (event : Bool → Prop) :
    ((addressOracle weak).call i).probability event x =
      weak.probability event (fun u => x (.inl i, u)) := by
  change (weak.substitute _).probability event x = _
  rw [FiniteRandomizedTree.probability_substitute]
  rfl

noncomputable def exactEntryTree (g : BoolFn U) (a : Fin k → Bool) :
    DecisionTree (ApproxIndexCoordinates k × U) Bool :=
  (DecisionTree.readCoordinates (fun u : U => (.inr (a, true), u))).mapOutput g

@[simp] theorem exactEntryTree_eval (g : BoolFn U) (a : Fin k → Bool)
    (x : ApproxIndexCoordinates k × U → Bool) :
    (exactEntryTree g a).eval x = entry (blockValues g x) a := by
  simp [exactEntryTree, entry, blockValues]

theorem exactEntryTree_depth_le (g : BoolFn U) (a : Fin k → Bool) :
    (exactEntryTree g a).depth ≤ Fintype.card U := by
  simpa only [exactEntryTree, DecisionTree.depth_mapOutput] using
    DecisionTree.depth_readCoordinates_le
      (fun u : U => ((Sum.inr (a, true) : ApproxIndexCoordinates k), u))

/-- Estimate the address, then exactly evaluate its selected value block. -/
noncomputable def composedAlgorithm (g : BoolFn U) (weak : FiniteRandomizedTree Seed U Bool) :
    FiniteRandomizedTree (Fin k → Seed) (ApproxIndexCoordinates k × U) Bool :=
  (addressOracle weak).parallel.bindDeterministic (exactEntryTree g)

theorem composedAlgorithm_depthBound (g : BoolFn U) (weak : FiniteRandomizedTree Seed U Bool)
    {cost : ℕ} (hcost : weak.DepthBound cost) :
    (composedAlgorithm (k := k) g weak).DepthBound (k * cost + Fintype.card U) := by
  apply FiniteRandomizedTree.depthBound_bindDeterministic
  · have h := (addressOracle (k := k) weak).parallel_depthBound (cost := cost) (by
      intro i seed
      exact (DecisionTree.depth_substitute_le _ _).trans (hcost seed))
    simpa only [Fintype.card_fin] using h
  · exact exactEntryTree_depth_le g

theorem count_errors_eq_distance (a target : Fin k → Bool) :
    BernoulliProduct.count (fun i => decide (a i ≠ target i)) = (distance target a : ℝ) := by
  classical
  simp [BernoulliProduct.count, distance, Finset.card_filter, ne_comm]

theorem composedAlgorithm_error_le_address_tail (g : BoolFn U)
    (weak : FiniteRandomizedTree Seed U Bool) (radius : ℕ)
    (x : ApproxIndexCoordinates k × U → Bool) (z : Bool)
    (hvalid : Valid radius (blockValues g x) z) :
    (composedAlgorithm g weak).probability (fun b => b ≠ z) x ≤
      (addressOracle weak).parallel.probability
        (fun a => radius < distance (address (blockValues g x)) a) x := by
  unfold composedAlgorithm
  rw [FiniteRandomizedTree.probability_bindDeterministic]
  apply FiniteRandomizedTree.probability_mono
  intro a ha
  rw [exactEntryTree_eval] at ha
  by_contra hn
  exact ha (hvalid.2 a (Nat.le_of_not_lt hn))

omit [Fintype U] in
/-- The actual independent address sampler obeys the finite Chebyshev bound.
The real threshold hypothesis accommodates any chosen integer radius. -/
theorem address_tail_le (g : BoolFn U) (weak : FiniteRandomizedTree Seed U Bool)
    (bias gap : ℝ) (hgap : 0 < gap)
    (hweak : ∀ input, 1 / 2 + bias ≤ weak.probability (fun b => b = g input) input)
    (radius : ℕ) (hthreshold : (k : ℝ) * (1 / 2 - bias) + gap ≤ radius)
    (x : ApproxIndexCoordinates k × U → Bool) :
    (addressOracle weak).parallel.probability
      (fun a => radius < distance (address (blockValues g x)) a) x ≤
      (k : ℝ) / (4 * gap ^ 2) := by
  classical
  let target := address (blockValues g x)
  let errors := (addressOracle weak).answerMap (fun i b => decide (b ≠ target i))
  have herr (i : Fin k) : errors.acceptProbability x i ≤ 1 / 2 - bias := by
    change ((addressOracle weak).answerMap _).acceptProbability x i ≤ _
    rw [RandomizedOracle.acceptProbability_answerMap]
    simp only [decide_eq_true_eq]
    rw [addressOracle_probability, FiniteRandomizedTree.probability_not]
    have h := hweak (fun u => x (.inl i, u))
    change 1 / 2 + bias ≤ weak.probability (fun b => b = target i) (fun u => x (.inl i, u)) at h
    linarith
  have hmean : (∑ i, errors.acceptProbability x i) + gap ≤ (radius : ℝ) := by
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => herr i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    linarith
  have htail := BernoulliProduct.upper_tail_of_mean_le (errors.acceptProbability x)
    (errors.acceptProbability_bounds x) (radius : ℝ) gap hgap hmean
  have hevent : errors.parallel.probability
      (fun a => (radius : ℝ) < BernoulliProduct.count a) x =
      (addressOracle weak).parallel.probability
        (fun a => radius < distance target a) x := by
    rw [RandomizedOracle.probability_parallel_answerMap]
    congr 1
    funext a
    rw [count_errors_eq_distance]
    exact propext Nat.cast_lt
  rw [← hevent, RandomizedOracle.probability_parallel_event]
  simpa only [Fintype.card_fin] using htail

theorem composedAlgorithm_error_le (g : BoolFn U) (weak : FiniteRandomizedTree Seed U Bool)
    (bias gap : ℝ) (hgap : 0 < gap)
    (hweak : ∀ input, 1 / 2 + bias ≤ weak.probability (fun b => b = g input) input)
    (radius : ℕ) (hthreshold : (k : ℝ) * (1 / 2 - bias) + gap ≤ radius)
    (x : ApproxIndexCoordinates k × U → Bool) (z : Bool)
    (hvalid : Valid radius (blockValues g x) z) :
    (composedAlgorithm g weak).probability (fun b => b ≠ z) x ≤ (k : ℝ) / (4 * gap ^ 2) :=
  (composedAlgorithm_error_le_address_tail g weak radius x z hvalid).trans
    (address_tail_le g weak bias gap hgap hweak radius hthreshold x)

end QueryComplexity.ApproxIndex
