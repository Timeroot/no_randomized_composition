import QueryComplexity.PrivateKernels

open scoped BigOperators

namespace QueryComplexity.ProductKernels

open FiniteProbability PrivateKernels

variable {T A J : Type*} [Fintype T] [DecidableEq T] [Fintype A] [DecidableEq A]
  [Fintype J] [DecidableEq J]

abbrev Kernel (T A J : Type*) := T → A → Weight (J → Bool)

def Normalized (K : Kernel T A J) : Prop :=
  ∀ t a, Nonnegative (K t a) ∧ mass (K t a) = 1

def productWeight (K : Kernel T A J) (s : T → A) (x : T → J → Bool) : ℝ :=
  ∏ t, K t (s t) (x t)

def score (f : (T → A) → Bool) (μ : Weight (T → A)) (K : Kernel T A J)
    (tree : DecisionTree (T × J) Bool) : ℝ :=
  ∑ s, μ s * ∑ x, productWeight K s x *
    (if tree.eval (fun p => x p.1 p.2) = f s then (1 : ℝ) else 0)

theorem productWeight_mass {K : Kernel T A J} (hK : Normalized K) (s : T → A) :
    (∑ x, productWeight K s x) = 1 := by
  unfold productWeight
  rw [← Fintype.prod_sum]
  change (∏ t, mass (K t (s t))) = 1
  simp only [fun t => (hK t (s t)).2, Finset.prod_const_one]

theorem score_leaf (f : (T → A) → Bool) (μ : Weight (T → A))
    {K : Kernel T A J} (hK : Normalized K) (b : Bool) :
    score f μ K (.leaf b) = labelMass f μ b := by
  unfold score labelMass mass restrict
  apply Finset.sum_congr rfl
  intro s _
  simp only [DecisionTree.eval]
  by_cases hb : b = f s
  · simp [hb, productWeight_mass hK s]
  · simp [hb, Ne.symm hb]

noncomputable def conditioned (K : Kernel T A J) (t : T) (j : J) (b : Bool) : Kernel T A J :=
  Function.update K t (fun a => conditional (K t a) j b)

theorem conditioned_normalized {K : Kernel T A J} (hK : Normalized K)
    (t : T) (j : J) (b : Bool) : Normalized (conditioned K t j b) := by
  intro u a
  by_cases hu : u = t
  · subst u
    simpa only [conditioned, Function.update_self] using
      And.intro (conditional_nonneg (hK t a).1 j b) (conditional_mass (hK t a).2 j b)
  · simpa only [conditioned, Function.update_of_ne hu] using hK u a

theorem conditioned_product {K : Kernel T A J} (hK : Normalized K)
    (t : T) (j : J) (b : Bool) (s : T → A) (x : T → J → Bool) :
    probability (K t (s t)) j b * productWeight (conditioned K t j b) s x =
      if x t j = b then productWeight K s x else 0 := by
  have hu : (fun u => conditioned K t j b u (s u) (x u)) =
      Function.update (fun u => K u (s u) (x u)) t (conditional (K t (s t)) j b (x t)) := by
    funext u
    by_cases h : u = t
    · subst u; simp [conditioned]
    · simp [conditioned, Function.update_of_ne h]
  unfold productWeight
  rw [hu, Finset.prod_update_of_mem (Finset.mem_univ t)]
  rw [← mul_assoc, conditional_factor (hK t (s t)).1]
  rw [← Finset.mul_prod_erase Finset.univ (fun u => K u (s u) (x u)) (Finset.mem_univ t)]
  simp only [DirectProduct.queried, restrict]
  split_ifs <;> simp [Finset.sdiff_singleton_eq_erase]

theorem score_node (f : (T → A) → Bool) (μ : Weight (T → A))
    {K : Kernel T A J} (hK : Normalized K) (t : T) (j : J)
    (zero one : DecisionTree (T × J) Bool) (p : Bool → ℝ)
    (hp : ∀ s, μ s ≠ 0 → ∀ b, probability (K t (s t)) j b = p b) :
    score f μ K (.node (t, j) zero one) =
      p false * score f μ (conditioned K t j false) zero +
      p true * score f μ (conditioned K t j true) one := by
  simp only [score, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : μ s = 0
  · simp [hs]
  rw [← hp s hs false, ← hp s hs true]
  simp only [mul_left_comm (probability _ _ _), Finset.mul_sum, ← mul_add,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  simp only [← mul_assoc]
  rw [mul_comm (productWeight (conditioned K t j false) s x), conditioned_product hK,
    mul_comm (productWeight (conditioned K t j true) s x), conditioned_product hK]
  cases hb : x t j <;> simp [DecisionTree.eval, hb]

def restrictSymbol (μ : Weight (T → A)) (t : T) (a : A) : Weight (T → A) :=
  fun s => if s t = a then μ s else 0

theorem restrictSymbol_nonneg {μ : Weight (T → A)} (hμ : Nonnegative μ) (t : T) (a : A) :
    Nonnegative (restrictSymbol μ t a) := by
  intro s
  unfold restrictSymbol
  split_ifs <;> first | exact hμ s | exact le_rfl

theorem score_split (f : (T → A) → Bool) (μ : Weight (T → A))
    (K : Kernel T A J) (tree : DecisionTree (T × J) Bool) (t : T) :
    score f μ K tree = ∑ a, score f (restrictSymbol μ t a) K tree := by
  simp only [score]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp [restrictSymbol, ite_mul]

theorem score_node_le (f : (T → A) → Bool) (μ : Weight (T → A))
    {K : Kernel T A J} (hK : Normalized K) (t : T) (j : J)
    (zero one : DecisionTree (T × J) Bool) (a₀ : A) (V : ℝ)
    (hp : ∀ s, μ s ≠ 0 → ∀ b, probability (K t (s t)) j b = probability (K t a₀) j b)
    (hb : ∀ b, probability (K t a₀) j b ≠ 0 →
      score f μ (conditioned K t j b) (if b then one else zero) ≤ V) :
    score f μ K (.node (t, j) zero one) ≤ V := by
  have h (b : Bool) : probability (K t a₀) j b *
      score f μ (conditioned K t j b) (if b then one else zero) ≤
        probability (K t a₀) j b * V := by
    by_cases hz : probability (K t a₀) j b = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left (hb b hz) (probability_nonneg (hK t a₀).1 j b)
  rw [score_node f μ hK t j zero one _ hp]
  have hsum := probability_add (K t a₀) j
  rw [(hK t a₀).2] at hsum
  have h0 := h false
  have h1 := h true
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.true_eq] at h0 h1
  exact (add_le_add h0 h1).trans_eq (by rw [← add_mul, hsum, one_mul])

end QueryComplexity.ProductKernels
