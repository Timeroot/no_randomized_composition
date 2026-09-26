import QueryComplexity.Algorithms

/-! Bounded adaptive programs calling independent randomized query algorithms.
The sample space and every resulting binary decision tree are explicit. -/

open scoped BigOperators

namespace QueryComplexity

universe u v w

namespace FiniteRandomizedTree

noncomputable def expectation {Seed : Type u} [Fintype Seed] {T : Type v} {Output : Type w}
    (algorithm : FiniteRandomizedTree Seed T Output) (payoff : Output → ℝ) (x : T → Bool) : ℝ :=
  ∑ s, algorithm.weight s * payoff ((algorithm.tree s).eval x)

theorem probability_eq_expectation {Seed : Type u} [Fintype Seed] {T : Type v} {Output : Type w}
    (algorithm : FiniteRandomizedTree Seed T Output) (event : Output → Prop) [DecidablePred event]
    (x : T → Bool) :
    algorithm.probability event x = algorithm.expectation (fun a => if event a then 1 else 0) x := by
  classical
  unfold probability expectation
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> simp_all

theorem expectation_bool {Seed : Type u} [Fintype Seed] {T : Type v}
    (algorithm : FiniteRandomizedTree Seed T Bool) (payoff : Bool → ℝ) (x : T → Bool) :
    algorithm.expectation payoff x =
      (1 - algorithm.probability (fun b => b = true) x) * payoff false +
        algorithm.probability (fun b => b = true) x * payoff true := by
  classical
  have hpoint (s : Seed) : algorithm.weight s * payoff ((algorithm.tree s).eval x) =
      algorithm.weight s * payoff false +
        (if (algorithm.tree s).eval x = true then algorithm.weight s else 0) *
          (payoff true - payoff false) := by
    cases (algorithm.tree s).eval x
    · simp
    · simp
      ring
  unfold expectation
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, algorithm.weight_sum]
  have heq : (∑ s, if (algorithm.tree s).eval x = true then algorithm.weight s else 0) =
      algorithm.probability (fun b => b = true) x := by
    unfold probability
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> rfl
  rw [heq]
  ring

@[simp] theorem probability_map_not_true {Seed : Type u} [Fintype Seed] {T : Type v}
    (algorithm : FiniteRandomizedTree Seed T Bool) (x : T → Bool) :
    (algorithm.mapOutput Bool.not).probability (fun b => b = true) x =
      algorithm.probability (fun b => b = false) x := by
  rw [probability_mapOutput]
  congr 1
  funext b
  cases b <;> simp

@[simp] theorem probability_map_not_false {Seed : Type u} [Fintype Seed] {T : Type v}
    (algorithm : FiniteRandomizedTree Seed T Bool) (x : T → Bool) :
    (algorithm.mapOutput Bool.not).probability (fun b => b = false) x =
      algorithm.probability (fun b => b = true) x := by
  rw [probability_mapOutput]
  congr 1
  funext b
  cases b <;> simp

end FiniteRandomizedTree

/-- An oracle family with a common finite source of randomness. -/
structure RandomizedOracle (Seed : Type u) [Fintype Seed] (Query : Type v) (T : Type w) where
  weight : Seed → ℝ
  weight_nonneg : ∀ s, 0 ≤ weight s
  weight_sum : (∑ s, weight s) = 1
  tree : Query → Seed → DecisionTree T Bool

namespace RandomizedOracle

variable {Seed : Type u} [Fintype Seed] {Query : Type v} {T : Type w}

def call (oracle : RandomizedOracle Seed Query T) (query : Query) :
    FiniteRandomizedTree Seed T Bool :=
  ⟨oracle.tree query, oracle.weight, oracle.weight_nonneg, oracle.weight_sum⟩

noncomputable def acceptProbability (oracle : RandomizedOracle Seed Query T)
    (x : T → Bool) (query : Query) : ℝ :=
  (oracle.call query).probability (fun b => b = true) x

theorem acceptProbability_bounds (oracle : RandomizedOracle Seed Query T)
    (x : T → Bool) (query : Query) :
    0 ≤ oracle.acceptProbability x query ∧ oracle.acceptProbability x query ≤ 1 :=
  ⟨(oracle.call query).probability_nonneg _ _, (oracle.call query).probability_le_one _ _⟩

def queryMap {Query' : Type*} (oracle : RandomizedOracle Seed Query T) (mapping : Query' → Query) :
    RandomizedOracle Seed Query' T where
  weight := oracle.weight
  weight_nonneg := oracle.weight_nonneg
  weight_sum := oracle.weight_sum
  tree query := oracle.tree (mapping query)

@[simp] theorem acceptProbability_queryMap {Query' : Type*}
    (oracle : RandomizedOracle Seed Query T) (mapping : Query' → Query)
    (x : T → Bool) (query : Query') :
    (oracle.queryMap mapping).acceptProbability x query = oracle.acceptProbability x (mapping query) := rfl

def flipped (oracle : RandomizedOracle Seed Query T) : RandomizedOracle Seed Query T where
  weight := oracle.weight
  weight_nonneg := oracle.weight_nonneg
  weight_sum := oracle.weight_sum
  tree query seed := (oracle.tree query seed).mapOutput Bool.not

@[simp] theorem acceptProbability_flipped (oracle : RandomizedOracle Seed Query T)
    (x : T → Bool) (query : Query) :
    oracle.flipped.acceptProbability x query = 1 - oracle.acceptProbability x query := by
  change ((oracle.call query).mapOutput Bool.not).probability (fun b => b = true) x = _
  rw [FiniteRandomizedTree.probability_map_not_true, FiniteRandomizedTree.probability_false]
  rfl

/-- Coordinate substitutions of one algorithm share exactly the same random weights. -/
def ofSubstitutions {U : Type*} (algorithm : FiniteRandomizedTree Seed U Bool)
    (substitution : Query → BitSubstitution T U) : RandomizedOracle Seed Query T where
  weight := algorithm.weight
  weight_nonneg := algorithm.weight_nonneg
  weight_sum := algorithm.weight_sum
  tree query seed := (algorithm.tree seed).substitute (substitution query)

def Seeds (Seed : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => Seed × Seeds Seed n

instance instFintypeSeeds (Seed : Type u) [Fintype Seed] (n : ℕ) : Fintype (Seeds Seed n) :=
  match n with
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => by
      letI : Fintype (Seeds Seed n) := instFintypeSeeds Seed n
      exact inferInstanceAs (Fintype (Seed × Seeds Seed n))

noncomputable def seedsWeight (oracle : RandomizedOracle Seed Query T) :
    (n : ℕ) → Seeds Seed n → ℝ
  | 0, _ => 1
  | n + 1, seed => oracle.weight seed.1 * oracle.seedsWeight n seed.2

@[simp] theorem seedsWeight_queryMap {Query' : Type*}
    (oracle : RandomizedOracle Seed Query T) (mapping : Query' → Query)
    (n : ℕ) (seed : Seeds Seed n) :
    (oracle.queryMap mapping).seedsWeight n seed = oracle.seedsWeight n seed := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change oracle.weight seed.1 * (oracle.queryMap mapping).seedsWeight n seed.2 =
        oracle.weight seed.1 * oracle.seedsWeight n seed.2
      rw [ih]

theorem seedsWeight_nonneg (oracle : RandomizedOracle Seed Query T) (n : ℕ)
    (seed : Seeds Seed n) : 0 ≤ oracle.seedsWeight n seed := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (oracle.weight_nonneg _) (ih _)

theorem seedsWeight_sum (oracle : RandomizedOracle Seed Query T) (n : ℕ) :
    (∑ seed : Seeds Seed n, oracle.seedsWeight n seed) = 1 := by
  induction n with
  | zero => simp [seedsWeight, Seeds]
  | succ n ih =>
      change (∑ seed : Seed × Seeds Seed n, oracle.weight seed.1 * oracle.seedsWeight n seed.2) = 1
      simp [Fintype.sum_prod_type, ← Finset.mul_sum, ih, oracle.weight_sum]

variable {State Output : Type*}

/-- Compile a bounded randomized-oracle program, using one independent seed
per call and the same original binary decision-tree model. -/
def compile (oracle : RandomizedOracle Seed Query T)
    (step : State → QueryStep Query Bool State Output) (fallback : Output) :
    (n : ℕ) → Seeds Seed n → State → DecisionTree T Output
  | 0, _, _ => .leaf fallback
  | n + 1, seed, state =>
      match step state with
      | .done answer => .leaf answer
      | .ask query next => (oracle.tree query seed.1).bind
          (fun answer => oracle.compile step fallback n seed.2 (next answer))

theorem depth_compile_le (oracle : RandomizedOracle Seed Query T)
    (step : State → QueryStep Query Bool State Output) (fallback : Output) {cost : ℕ}
    (hcost : ∀ query seed, (oracle.tree query seed).depth ≤ cost)
    (n : ℕ) (seed : Seeds Seed n) (state : State) :
    (oracle.compile step fallback n seed state).depth ≤ n * cost := by
  induction n generalizing state with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      cases hs : step state with
      | done answer => simp [compile, hs, DecisionTree.depth]
      | ask query next =>
          have h := DecisionTree.depth_bind_le_add (oracle.tree query seed.1)
            (fun answer => oracle.compile step fallback n seed.2 (next answer)) (hcost _ _)
            (fun answer => ih seed.2 (next answer))
          simpa [compile, hs, Nat.succ_mul, Nat.add_comm] using h

noncomputable def algorithm (oracle : RandomizedOracle Seed Query T)
    (step : State → QueryStep Query Bool State Output) (fallback : Output) (n : ℕ) (state : State) :
    FiniteRandomizedTree (Seeds Seed n) T Output where
  tree seed := oracle.compile step fallback n seed state
  weight := oracle.seedsWeight n
  weight_nonneg := oracle.seedsWeight_nonneg n
  weight_sum := oracle.seedsWeight_sum n

theorem algorithm_depthBound (oracle : RandomizedOracle Seed Query T)
    (step : State → QueryStep Query Bool State Output) (fallback : Output) {cost : ℕ}
    (hcost : ∀ query seed, (oracle.tree query seed).depth ≤ cost) (n : ℕ) (state : State) :
    (oracle.algorithm step fallback n state).DepthBound (n * cost) :=
  fun seed => oracle.depth_compile_le step fallback hcost n seed state

/-- The finite probability recurrence of the compiled program. -/
noncomputable def value (p : Query → ℝ) (step : State → QueryStep Query Bool State Output)
    (payoff : Output → ℝ) (fallback : Output) : ℕ → State → ℝ
  | 0, _ => payoff fallback
  | n + 1, state =>
      match step state with
      | .done answer => payoff answer
      | .ask query next => (1 - p query) * value p step payoff fallback n (next false) +
          p query * value p step payoff fallback n (next true)

theorem expectation_algorithm (oracle : RandomizedOracle Seed Query T)
    (step : State → QueryStep Query Bool State Output) (payoff : Output → ℝ) (fallback : Output)
    (n : ℕ) (state : State) (x : T → Bool) :
    (oracle.algorithm step fallback n state).expectation payoff x =
      value (oracle.acceptProbability x) step payoff fallback n state := by
  induction n generalizing state with
  | zero => simp [algorithm, compile, FiniteRandomizedTree.expectation, seedsWeight, Seeds,
      DecisionTree.eval, value]
  | succ n ih =>
      cases hs : step state with
      | done answer =>
          unfold FiniteRandomizedTree.expectation algorithm
          simp only [compile, hs, DecisionTree.eval]
          rw [← Finset.sum_mul, oracle.seedsWeight_sum]
          simp [value, hs]
      | ask query next =>
          unfold FiniteRandomizedTree.expectation algorithm
          change (∑ seed : Seed × Seeds Seed n,
            (oracle.weight seed.1 * oracle.seedsWeight n seed.2) *
              payoff ((oracle.compile step fallback (n + 1) seed state).eval x)) = _
          simp only [compile, hs, DecisionTree.eval_bind, Fintype.sum_prod_type]
          have htail (seed : Seed) :
              (∑ tail, oracle.seedsWeight n tail *
                payoff ((oracle.compile step fallback n tail
                  (next ((oracle.tree query seed).eval x))).eval x)) =
              value (oracle.acceptProbability x) step payoff fallback n
                (next ((oracle.tree query seed).eval x)) :=
            ih (next ((oracle.tree query seed).eval x))
          simp only [mul_assoc, ← Finset.mul_sum, htail]
          have hb := (oracle.call query).expectation_bool
            (fun answer => value (oracle.acceptProbability x) step payoff fallback n (next answer)) x
          simpa only [FiniteRandomizedTree.expectation, call, acceptProbability, value, hs] using hb

end RandomizedOracle
end QueryComplexity
