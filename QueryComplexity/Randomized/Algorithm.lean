import QueryComplexity.DecisionTree.Operations

/-!
# Finite randomized decision trees

Finite probability distributions on trees, independent combinations of
algorithms, and their relationship to `HasRandomizedBound`.
-/

open scoped BigOperators

namespace QueryComplexity

universe u v w

/-- A finite distribution on deterministic trees, with an arbitrary finite
seed type. Its normalization is part of the data. -/
structure FiniteRandomizedTree (Seed : Type u) [Fintype Seed] (T : Type v) (Output : Type w) where
  tree : Seed → DecisionTree T Output
  weight : Seed → ℝ
  weight_nonneg : ∀ s, 0 ≤ weight s
  weight_sum : (∑ s, weight s) = 1

namespace FiniteRandomizedTree

variable {Seed : Type u} [Fintype Seed] {T : Type v} {Output : Type w}

/-- Choose a seed uniformly from a nonempty finite type. -/
noncomputable def uniform [Nonempty Seed] (tree : Seed → DecisionTree T Output) :
    FiniteRandomizedTree Seed T Output where
  tree := tree
  weight _ := (Fintype.card Seed : ℝ)⁻¹
  weight_nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  weight_sum := by
    have hcard : (Fintype.card Seed : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [hcard]

def DepthBound (algorithm : FiniteRandomizedTree Seed T Output) (d : ℕ) : Prop :=
  ∀ s, (algorithm.tree s).depth ≤ d

noncomputable def probability (algorithm : FiniteRandomizedTree Seed T Output)
    (event : Output → Prop) (x : T → Bool) : ℝ := by
  classical
  exact ∑ s, if event ((algorithm.tree s).eval x) then algorithm.weight s else 0

theorem probability_nonneg (algorithm : FiniteRandomizedTree Seed T Output)
    (event : Output → Prop) (x : T → Bool) : 0 ≤ algorithm.probability event x := by
  classical
  refine Finset.sum_nonneg fun s _ => ?_
  split_ifs
  · exact algorithm.weight_nonneg s
  · exact le_rfl

theorem probability_le_one (algorithm : FiniteRandomizedTree Seed T Output)
    (event : Output → Prop) (x : T → Bool) : algorithm.probability event x ≤ 1 := by
  classical
  rw [← algorithm.weight_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  split_ifs
  · exact le_rfl
  · exact algorithm.weight_nonneg s

theorem probability_mono (algorithm : FiniteRandomizedTree Seed T Output)
    {p q : Output → Prop} (hpq : ∀ a, p a → q a) (x : T → Bool) :
    algorithm.probability p x ≤ algorithm.probability q x := by
  classical
  refine Finset.sum_le_sum fun s _ => ?_
  split_ifs with hp hq hq
  · rfl
  · exact (hq (hpq _ hp)).elim
  · exact algorithm.weight_nonneg s
  · rfl

@[simp] theorem probability_true (algorithm : FiniteRandomizedTree Seed T Output)
    (x : T → Bool) : algorithm.probability (fun _ => True) x = 1 := by
  unfold probability
  simpa using algorithm.weight_sum

theorem probability_or_of_disjoint (algorithm : FiniteRandomizedTree Seed T Output)
    (p q : Output → Prop) (hdisjoint : ∀ a, ¬ (p a ∧ q a)) (x : T → Bool) :
    algorithm.probability (fun a => p a ∨ q a) x =
      algorithm.probability p x + algorithm.probability q x := by
  classical
  unfold probability
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp_all

theorem probability_not (algorithm : FiniteRandomizedTree Seed T Output)
    (p : Output → Prop) (x : T → Bool) :
    algorithm.probability (fun a => ¬ p a) x = 1 - algorithm.probability p x := by
  classical
  have h := algorithm.probability_or_of_disjoint p (fun a => ¬ p a) (by simp) x
  have hall : (fun a => p a ∨ ¬ p a) = fun _ => True := by
    funext a
    apply propext
    tauto
  rw [hall, probability_true] at h
  linarith

/-- Apply a deterministic function to the output without making queries. -/
def mapOutput {Output' : Type*} (algorithm : FiniteRandomizedTree Seed T Output)
    (decode : Output → Output') : FiniteRandomizedTree Seed T Output' where
  tree s := (algorithm.tree s).mapOutput decode
  weight := algorithm.weight
  weight_nonneg := algorithm.weight_nonneg
  weight_sum := algorithm.weight_sum

@[simp] theorem depthBound_mapOutput {Output' : Type*}
    (algorithm : FiniteRandomizedTree Seed T Output) (decode : Output → Output') (d : ℕ) :
    (algorithm.mapOutput decode).DepthBound d ↔ algorithm.DepthBound d := by
  simp [DepthBound, mapOutput]

@[simp] theorem probability_mapOutput {Output' : Type*}
    (algorithm : FiniteRandomizedTree Seed T Output) (decode : Output → Output')
    (event : Output' → Prop) (x : T → Bool) :
    (algorithm.mapOutput decode).probability event x =
      algorithm.probability (fun a => event (decode a)) x := by
  classical
  unfold probability mapOutput
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [DecisionTree.eval_mapOutput]

/-- Lift an algorithm through a single-bit input substitution. -/
def substitute {U : Type*} (algorithm : FiniteRandomizedTree Seed T Output)
    (σ : BitSubstitution U T) : FiniteRandomizedTree Seed U Output where
  tree s := (algorithm.tree s).substitute σ
  weight := algorithm.weight
  weight_nonneg := algorithm.weight_nonneg
  weight_sum := algorithm.weight_sum

theorem depthBound_substitute {U : Type*} (algorithm : FiniteRandomizedTree Seed T Output)
    (σ : BitSubstitution U T) {d : ℕ} (h : algorithm.DepthBound d) :
    (algorithm.substitute σ).DepthBound d := by
  intro s
  exact ((algorithm.tree s).depth_substitute_le σ).trans (h s)

@[simp] theorem probability_substitute {U : Type*}
    (algorithm : FiniteRandomizedTree Seed T Output) (σ : BitSubstitution U T)
    (event : Output → Prop) (x : U → Bool) :
    (algorithm.substitute σ).probability event x = algorithm.probability event (σ.eval x) := by
  classical
  unfold probability substitute
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [DecisionTree.eval_substitute]

/-- Uniformly choose a member of a finite family of randomized algorithms. -/
noncomputable def uniformChoice {Choice : Type*} [Fintype Choice] [Nonempty Choice]
    (family : Choice → FiniteRandomizedTree Seed T Output) :
    FiniteRandomizedTree (Choice × Seed) T Output where
  tree s := (family s.1).tree s.2
  weight s := (Fintype.card Choice : ℝ)⁻¹ * (family s.1).weight s.2
  weight_nonneg s := mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    ((family s.1).weight_nonneg _)
  weight_sum := by
    have hcard : (Fintype.card Choice : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, weight_sum]
    simp [hcard]

theorem depthBound_uniformChoice {Choice : Type*} [Fintype Choice] [Nonempty Choice]
    (family : Choice → FiniteRandomizedTree Seed T Output) {d : ℕ}
    (h : ∀ s, (family s).DepthBound d) : (uniformChoice family).DepthBound d :=
  fun s => h s.1 s.2

theorem probability_uniformChoice {Choice : Type*} [Fintype Choice] [Nonempty Choice]
    (family : Choice → FiniteRandomizedTree Seed T Output)
    (event : Output → Prop) (x : T → Bool) :
    (uniformChoice family).probability event x =
      (Fintype.card Choice : ℝ)⁻¹ * ∑ s, (family s).probability event x := by
  classical
  unfold probability uniformChoice
  simp only [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

/-- A biased coin is a zero-query finite randomized tree. -/
def coin (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : FiniteRandomizedTree Bool T Bool where
  tree b := .leaf b
  weight b := if b then p else 1 - p
  weight_nonneg b := by cases b <;> simp [hp₀, sub_nonneg.mpr hp₁]
  weight_sum := by simp

theorem depthBound_coin (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    (coin (T := T) p hp₀ hp₁).DepthBound 0 := fun _ => le_rfl

@[simp] theorem probability_coin_true (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (x : T → Bool) :
    (coin p hp₀ hp₁).probability (fun b => b = true) x = p := by
  simp [probability, coin, DecisionTree.eval]

theorem probability_false (algorithm : FiniteRandomizedTree Seed T Bool) (x : T → Bool) :
    algorithm.probability (fun b => b = false) x = 1 - algorithm.probability (fun b => b = true) x := by
  have heq : (fun b : Bool => b = false) = fun b => ¬ b = true := by
    funext b
    cases b <;> simp
  rw [heq, probability_not]

/-- Independent sequential execution uses the product distribution of seeds. -/
def pair {Seed' : Type*} [Fintype Seed'] {Output' : Type*}
    (first : FiniteRandomizedTree Seed T Output)
    (second : FiniteRandomizedTree Seed' T Output') :
    FiniteRandomizedTree (Seed × Seed') T (Output × Output') where
  tree s := (first.tree s.1).pair (second.tree s.2)
  weight s := first.weight s.1 * second.weight s.2
  weight_nonneg s := mul_nonneg (first.weight_nonneg _) (second.weight_nonneg _)
  weight_sum := by
    simp [Fintype.sum_prod_type, ← Finset.mul_sum, first.weight_sum, second.weight_sum]

theorem depthBound_pair {Seed' : Type*} [Fintype Seed'] {Output' : Type*}
    (first : FiniteRandomizedTree Seed T Output)
    (second : FiniteRandomizedTree Seed' T Output') {d e : ℕ}
    (hfirst : first.DepthBound d) (hsecond : second.DepthBound e) :
    (first.pair second).DepthBound (d + e) := by
  intro s
  exact ((first.tree s.1).depth_pair_le (second.tree s.2)).trans
    (Nat.add_le_add (hfirst _) (hsecond _))

theorem probability_pair {Seed' : Type*} [Fintype Seed'] {Output' : Type*}
    (first : FiniteRandomizedTree Seed T Output)
    (second : FiniteRandomizedTree Seed' T Output')
    (p : Output → Prop) (q : Output' → Prop) (x : T → Bool) :
    (first.pair second).probability (fun a => p a.1 ∧ q a.2) x =
      first.probability p x * second.probability q x := by
  classical
  simp only [probability, pair, DecisionTree.eval_pair, Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp_all

/-- Independently run two Boolean algorithms and OR their outputs. -/
def or {Seed' : Type*} [Fintype Seed']
    (first : FiniteRandomizedTree Seed T Bool) (second : FiniteRandomizedTree Seed' T Bool) :
    FiniteRandomizedTree (Seed × Seed') T Bool :=
  (first.pair second).mapOutput (fun b => b.1 || b.2)

theorem depthBound_or {Seed' : Type*} [Fintype Seed']
    (first : FiniteRandomizedTree Seed T Bool) (second : FiniteRandomizedTree Seed' T Bool)
    {d e : ℕ} (hfirst : first.DepthBound d) (hsecond : second.DepthBound e) :
    (first.or second).DepthBound (d + e) := by
  simpa [or] using first.depthBound_pair second hfirst hsecond

theorem probability_or_true {Seed' : Type*} [Fintype Seed']
    (first : FiniteRandomizedTree Seed T Bool) (second : FiniteRandomizedTree Seed' T Bool)
    (x : T → Bool) :
    (first.or second).probability (fun b => b = true) x =
      first.probability (fun b => b = true) x +
        (1 - first.probability (fun b => b = true) x) * second.probability (fun b => b = true) x := by
  have heq : (fun b : Bool × Bool => (b.1 || b.2) = false) =
      fun b => b.1 = false ∧ b.2 = false := by
    funext b
    rcases b with ⟨a, b⟩
    cases a <;> cases b <;> simp
  have hfalse : (first.or second).probability (fun b => b = false) x =
      (1 - first.probability (fun b => b = true) x) *
        (1 - second.probability (fun b => b = true) x) := by
    unfold or
    rw [probability_mapOutput, heq,
      first.probability_pair second (fun b => b = false) (fun b => b = false) x,
      probability_false, probability_false]
  rw [probability_false] at hfalse
  nlinarith

/-- Arbitrary finite seed types give the same standard randomized model as
the `Fin m` distributions in `HasRandomizedBound`. -/
theorem toHasRandomizedBound (algorithm : FiniteRandomizedTree Seed T Bool)
    {f : BoolFn T} {d : ℕ} (hdepth : algorithm.DepthBound d)
    (hsuccess : ∀ x, (2 : ℝ) / 3 ≤ algorithm.probability (fun b => b = f x) x) :
    HasRandomizedBound f d := by
  classical
  let e := Fintype.equivFin Seed
  refine ⟨Fintype.card Seed, fun i => algorithm.tree (e.symm i),
    fun i => algorithm.weight (e.symm i), fun i => hdepth _,
    fun i => algorithm.weight_nonneg _, ?_, ?_⟩
  · exact (e.symm.sum_comp algorithm.weight).trans algorithm.weight_sum
  · intro x
    apply (hsuccess x).trans_eq
    unfold probability
    trans ∑ s, if (algorithm.tree s).eval x = f x then algorithm.weight s else 0
    · apply Finset.sum_congr rfl
      intro s _
      split_ifs <;> rfl
    · exact (e.symm.sum_comp
        (fun s => if (algorithm.tree s).eval x = f x then algorithm.weight s else 0)).symm

end FiniteRandomizedTree


/-- Every witness in the standard randomized-query model can be packaged as
a finite randomized tree with error at most `1/3` on every input. -/
theorem HasRandomizedBound.exists_algorithm {T : Type u} {f : BoolFn T} {d : ℕ}
    (h : HasRandomizedBound f d) :
    ∃ m, ∃ algorithm : FiniteRandomizedTree (Fin m) T Bool,
      algorithm.DepthBound d ∧
        ∀ x, algorithm.probability (fun b => b ≠ f x) x ≤ 1 / 3 := by
  classical
  rcases h with ⟨m, tree, weight, hdepth, hnonneg, hmass, hsuccess⟩
  let algorithm : FiniteRandomizedTree (Fin m) T Bool := ⟨tree, weight, hnonneg, hmass⟩
  refine ⟨m, algorithm, hdepth, ?_⟩
  intro x
  have hprob : algorithm.probability (fun b => b = f x) x =
      ∑ s, if (tree s).eval x = f x then weight s else 0 := by
    unfold FiniteRandomizedTree.probability algorithm
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs <;> rfl
  have hn := algorithm.probability_not (fun b => b = f x) x
  rw [hprob] at hn
  rw [hn]
  grind [hsuccess x]

end QueryComplexity
