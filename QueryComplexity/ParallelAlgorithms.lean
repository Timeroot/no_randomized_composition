import QueryComplexity.RandomizedPrograms
import QueryComplexity.BernoulliProduct

open scoped BigOperators

namespace QueryComplexity

namespace DecisionTree

variable {Q T A : Type*}

/-- Replace an abstract input query by an arbitrary Boolean decision tree. -/
def expand (tree : DecisionTree Q A) (replacement : Q → DecisionTree T Bool) : DecisionTree T A :=
  match tree with
  | .leaf answer => .leaf answer
  | .node query zero one => (replacement query).bind
      (fun answer => if answer then one.expand replacement else zero.expand replacement)

@[simp] theorem eval_expand (tree : DecisionTree Q A) (replacement : Q → DecisionTree T Bool)
    (x : T → Bool) :
    (tree.expand replacement).eval x = tree.eval (fun q => (replacement q).eval x) := by
  induction tree with
  | leaf answer => rfl
  | node query zero one hz ho =>
      simp only [expand, eval_bind]
      cases h : (replacement query).eval x <;> simp [h, eval, hz, ho]

theorem depth_expand_le (tree : DecisionTree Q A) (replacement : Q → DecisionTree T Bool)
    {cost : ℕ} (hcost : ∀ q, (replacement q).depth ≤ cost) :
    (tree.expand replacement).depth ≤ tree.depth * cost := by
  induction tree with
  | leaf answer => simp [expand, depth]
  | node query zero one hz ho =>
      have h := depth_bind_le_add (replacement query)
        (fun answer => if answer then one.expand replacement else zero.expand replacement)
        (hcost query) (e := max zero.depth one.depth * cost) (by
          intro answer
          cases answer
          · exact hz.trans (Nat.mul_le_mul_right cost (le_max_left _ _))
          · exact ho.trans (Nat.mul_le_mul_right cost (le_max_right _ _)))
      simpa [expand, depth, Nat.add_mul, Nat.add_comm] using h

end DecisionTree

namespace FiniteRandomizedTree

variable {Seed T Output : Type*} [Fintype Seed]

def bindDeterministic {Next : Type*} (algorithm : FiniteRandomizedTree Seed T Output)
    (next : Output → DecisionTree T Next) : FiniteRandomizedTree Seed T Next where
  tree seed := (algorithm.tree seed).bind next
  weight := algorithm.weight
  weight_nonneg := algorithm.weight_nonneg
  weight_sum := algorithm.weight_sum

theorem depthBound_bindDeterministic {Next : Type*} (algorithm : FiniteRandomizedTree Seed T Output)
    (next : Output → DecisionTree T Next) {d e : ℕ} (hd : algorithm.DepthBound d)
    (he : ∀ a, (next a).depth ≤ e) : (algorithm.bindDeterministic next).DepthBound (d + e) :=
  fun seed => DecisionTree.depth_bind_le_add _ _ (hd seed) he

theorem probability_bindDeterministic {Next : Type*} (algorithm : FiniteRandomizedTree Seed T Output)
    (next : Output → DecisionTree T Next) (event : Next → Prop) (x : T → Bool) :
    (algorithm.bindDeterministic next).probability event x =
      algorithm.probability (fun a => event ((next a).eval x)) x := by
  classical
  unfold probability bindDeterministic
  simp only [DecisionTree.eval_bind]

theorem expectation_eq_sum_output [Fintype Output] (algorithm : FiniteRandomizedTree Seed T Output)
    (payoff : Output → ℝ) (x : T → Bool) :
    algorithm.expectation payoff x =
      ∑ a, algorithm.probability (fun output => output = a) x * payoff a := by
  classical
  unfold expectation probability
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro seed _
  simp

theorem probability_eq_sum_output [Fintype Output] (algorithm : FiniteRandomizedTree Seed T Output)
    (event : Output → Prop) [DecidablePred event] (x : T → Bool) :
    algorithm.probability event x =
      ∑ a, if event a then algorithm.probability (fun output => output = a) x else 0 := by
  rw [probability_eq_expectation, expectation_eq_sum_output]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

theorem probability_exists_le_sum {J : Type*} [Fintype J]
    (algorithm : FiniteRandomizedTree Seed T Output) (event : J → Output → Prop) (x : T → Bool) :
    algorithm.probability (fun a => ∃ j, event j a) x ≤
      ∑ j, algorithm.probability (event j) x := by
  classical
  unfold probability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro seed _
  by_cases h : ∃ j, event j ((algorithm.tree seed).eval x)
  · rw [if_pos h]
    obtain ⟨j, hj⟩ := h
    calc
      _ = if event j ((algorithm.tree seed).eval x) then algorithm.weight seed else 0 :=
        (if_pos hj).symm
      _ ≤ _ := by
        apply Finset.single_le_sum (f := fun i =>
          if event i ((algorithm.tree seed).eval x) then algorithm.weight seed else 0)
          ?_ (Finset.mem_univ j)
        intro i _
        dsimp only
        split_ifs
        · exact algorithm.weight_nonneg seed
        · exact le_rfl
  · rw [if_neg h]
    exact Finset.sum_nonneg (fun i _ => by
      split_ifs
      · exact algorithm.weight_nonneg seed
      · exact le_rfl)

end FiniteRandomizedTree

namespace RandomizedOracle

variable {Seed I T : Type*} [Fintype Seed] [Fintype I] [DecidableEq I]

/-- Independently sample a seed for each requested coordinate. -/
noncomputable def parallelWeight (oracle : RandomizedOracle Seed I T) (seed : I → Seed) : ℝ :=
  ∏ i, oracle.weight (seed i)

omit [DecidableEq I] in
theorem parallelWeight_nonneg (oracle : RandomizedOracle Seed I T) (seed : I → Seed) :
    0 ≤ oracle.parallelWeight seed :=
  Finset.prod_nonneg (fun i _ => oracle.weight_nonneg (seed i))

theorem parallelWeight_sum (oracle : RandomizedOracle Seed I T) :
    ∑ seed, oracle.parallelWeight seed = 1 := by
  classical
  have h := Fintype.prod_sum (fun (_ : I) (seed : Seed) => oracle.weight seed)
  simpa [parallelWeight, oracle.weight_sum] using h.symm

/-- Read all oracle outputs, using independent seeds but the same underlying input. -/
noncomputable def parallel (oracle : RandomizedOracle Seed I T) :
    FiniteRandomizedTree (I → Seed) T (I → Bool) where
  tree seed := (DecisionTree.readCoordinates (id : I → I)).expand (fun i => oracle.tree i (seed i))
  weight := oracle.parallelWeight
  weight_nonneg := oracle.parallelWeight_nonneg
  weight_sum := oracle.parallelWeight_sum

@[simp] theorem eval_parallel (oracle : RandomizedOracle Seed I T) (seed : I → Seed)
    (x : T → Bool) :
    (oracle.parallel.tree seed).eval x = fun i => (oracle.tree i (seed i)).eval x := by
  simp [parallel]

theorem parallel_depthBound (oracle : RandomizedOracle Seed I T) {cost : ℕ}
    (hcost : ∀ i seed, (oracle.tree i seed).depth ≤ cost) :
    oracle.parallel.DepthBound (Fintype.card I * cost) := by
  intro seed
  exact (DecisionTree.depth_expand_le _ _ (fun i => hcost i (seed i))).trans
    (Nat.mul_le_mul_right cost (DecisionTree.depth_readCoordinates_le _))

theorem probability_parallel_output (oracle : RandomizedOracle Seed I T) (x : T → Bool)
    (output : I → Bool) :
    oracle.parallel.probability (fun a => a = output) x =
      ∏ i, (oracle.call i).probability (fun b => b = output i) x := by
  classical
  have hpoint (seed : I → Seed) :
      (if (fun i => (oracle.tree i (seed i)).eval x) = output then oracle.parallelWeight seed else 0) =
        ∏ i, if (oracle.tree i (seed i)).eval x = output i then oracle.weight (seed i) else 0 := by
    by_cases heq : (fun i => (oracle.tree i (seed i)).eval x) = output
    · simp only [if_pos heq, parallelWeight]
      apply Finset.prod_congr rfl
      intro i _
      rw [if_pos (congrFun heq i)]
    · rw [if_neg heq]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp heq
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  unfold FiniteRandomizedTree.probability
  simp only [eval_parallel]
  change (∑ seed, if (fun i => (oracle.tree i (seed i)).eval x) = output
      then oracle.parallelWeight seed else 0) = _
  simp_rw [hpoint]
  simpa only [call] using (Fintype.prod_sum
    (fun (i : I) (seed : Seed) =>
      if (oracle.tree i seed).eval x = output i then oracle.weight seed else 0)).symm

theorem probability_parallel_bernoulli (oracle : RandomizedOracle Seed I T) (x : T → Bool)
    (output : I → Bool) :
    oracle.parallel.probability (fun a => a = output) x =
      BernoulliProduct.weight (oracle.acceptProbability x) output := by
  rw [probability_parallel_output]
  apply Finset.prod_congr rfl
  intro i _
  cases h : output i
  · simpa [h, acceptProbability] using (oracle.call i).probability_false x
  · simp [acceptProbability]

theorem probability_parallel_event (oracle : RandomizedOracle Seed I T) (x : T → Bool)
    (event : (I → Bool) → Prop) [DecidablePred event] :
    oracle.parallel.probability event x =
      ∑ a, if event a then BernoulliProduct.weight (oracle.acceptProbability x) a else 0 := by
  rw [FiniteRandomizedTree.probability_eq_sum_output]
  simp_rw [probability_parallel_bernoulli]

theorem probability_parallel_coordinate (oracle : RandomizedOracle Seed I T) (x : T → Bool)
    (i : I) (b : Bool) :
    oracle.parallel.probability (fun a => a i = b) x =
      (oracle.call i).probability (fun a => a = b) x := by
  classical
  rw [probability_parallel_event]
  have hpoint (a : I → Bool) :
      (if a i = b then BernoulliProduct.weight (oracle.acceptProbability x) a else 0) =
        BernoulliProduct.weight (oracle.acceptProbability x) a * (if a i = b then 1 else 0) := by
    split_ifs <;> simp
  simp_rw [hpoint]
  rw [BernoulliProduct.expectation_split (oracle.acceptProbability x) i]
  have heval (c : Bool) (rest : {j // j ≠ i} → Bool) :
      ((Equiv.funSplitAt i Bool).symm (c, rest)) i = c := by
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  simp only [heval]
  rw [← Finset.sum_mul, BernoulliProduct.weight_mass]
  cases b
  · simp [FiniteRandomizedTree.probability_false, acceptProbability]
  · simp [acceptProbability]

def answerMap (oracle : RandomizedOracle Seed I T) (mapping : I → Bool → Bool) :
    RandomizedOracle Seed I T where
  weight := oracle.weight
  weight_nonneg := oracle.weight_nonneg
  weight_sum := oracle.weight_sum
  tree i seed := (oracle.tree i seed).mapOutput (mapping i)

omit [Fintype I] [DecidableEq I] in
theorem acceptProbability_answerMap (oracle : RandomizedOracle Seed I T)
    (mapping : I → Bool → Bool) (x : T → Bool) (i : I) :
    (oracle.answerMap mapping).acceptProbability x i =
      (oracle.call i).probability (fun b => mapping i b = true) x := by
  change ((oracle.call i).mapOutput (mapping i)).probability _ x = _
  rw [FiniteRandomizedTree.probability_mapOutput]

theorem probability_parallel_answerMap (oracle : RandomizedOracle Seed I T)
    (mapping : I → Bool → Bool) (event : (I → Bool) → Prop) (x : T → Bool) :
    (oracle.answerMap mapping).parallel.probability event x =
      oracle.parallel.probability (fun a => event (fun i => mapping i (a i))) x := by
  classical
  unfold FiniteRandomizedTree.probability
  apply Finset.sum_congr rfl
  intro seed _
  simp only [eval_parallel, answerMap, DecisionTree.eval_mapOutput]
  rfl

end RandomizedOracle

end QueryComplexity
