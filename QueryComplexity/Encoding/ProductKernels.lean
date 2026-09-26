import QueryComplexity.Encoding.AdaptivePrivacy

/-! Private conditional kernels and independent products of encoded cells. -/

open scoped BigOperators

namespace QueryComplexity.PrivateKernels

open FiniteProbability DirectProduct AdaptivePrivacy

variable {J A : Type*} [Fintype J] [DecidableEq J]

def Private (r : ℕ) (K : A → Weight (J → Bool)) : Prop :=
  ∀ a b trace, trace.length ≤ r → mass (traceWeight (K a) trace) =
    mass (traceWeight (K b) trace)

def probability (K : Weight (J → Bool)) (j : J) (b : Bool) : ℝ :=
  mass (queried K j b)

noncomputable def conditional (K : Weight (J → Bool)) (j : J) (b : Bool) :
    Weight (J → Bool) :=
  if probability K j b = 0 then K else fun x => queried K j b x / probability K j b

theorem probability_nonneg {K : Weight (J → Bool)} (hK : Nonnegative K) (j : J) (b : Bool) :
    0 ≤ probability K j b := mass_nonnegative (queried_nonnegative hK j b)

theorem probability_add (K : Weight (J → Bool)) (j : J) :
    probability K j false + probability K j true = mass K := mass_restrict_add K _

theorem conditional_nonneg {K : Weight (J → Bool)} (hK : Nonnegative K) (j : J) (b : Bool) :
    Nonnegative (conditional K j b) := by
  intro x
  unfold conditional
  split_ifs
  · exact hK x
  · exact div_nonneg (queried_nonnegative hK j b x) (probability_nonneg hK j b)

theorem conditional_mass {K : Weight (J → Bool)} (hK : mass K = 1) (j : J) (b : Bool) :
    mass (conditional K j b) = 1 := by
  unfold conditional
  split_ifs with h
  · exact hK
  · simp only [mass, ← Finset.sum_div]
    exact div_self h

theorem conditional_factor {K : Weight (J → Bool)} (hK : Nonnegative K)
    (j : J) (b : Bool) (x : J → Bool) :
    probability K j b * conditional K j b x = queried K j b x := by
  by_cases hp : probability K j b = 0
  · have hx : queried K j b x = 0 := by
      have hle : queried K j b x ≤ probability K j b :=
        Finset.single_le_sum (fun y _ => queried_nonnegative hK j b y) (Finset.mem_univ x)
      exact le_antisymm (hle.trans_eq hp) (queried_nonnegative hK j b x)
    simp [hp, hx]
  · simp only [conditional, hp, if_false]
    field_simp

theorem traceWeight_div (K : Weight (J → Bool)) (trace : List (J × Bool)) (c : ℝ) :
    traceWeight (fun x => K x / c) trace = fun x => traceWeight K trace x / c := by
  funext x
  simp only [traceWeight_apply]
  split_ifs <;> simp

theorem conditional_trace_mass (K : Weight (J → Bool)) (j : J) (b : Bool)
    (hp : probability K j b ≠ 0) (trace : List (J × Bool)) :
    mass (traceWeight (conditional K j b) trace) =
      mass (traceWeight K ((j, b) :: trace)) / probability K j b := by
  simp only [conditional, hp, if_false, traceWeight_div, mass, ← Finset.sum_div, traceWeight]

theorem private_probability {K : A → Weight (J → Bool)} {r : ℕ}
    (hK : Private (r + 1) K) (a b : A) (j : J) (v : Bool) :
    probability (K a) j v = probability (K b) j v := by
  simpa only [traceWeight, probability] using hK a b [(j, v)] (by simp)

theorem private_conditional {K : A → Weight (J → Bool)} {r : ℕ}
    (hK : Private (r + 1) K) (j : J) (v : Bool) (a₀ : A)
    (hp : probability (K a₀) j v ≠ 0) :
    Private r (fun a => conditional (K a) j v) := by
  intro a b trace ht
  have ha := private_probability hK a a₀ j v
  have hb := private_probability hK b a₀ j v
  rw [conditional_trace_mass _ _ _ (by rwa [ha]),
    conditional_trace_mass _ _ _ (by rwa [hb]), ha, hb]
  rw [hK a b ((j, v) :: trace) (by simp; omega)]

theorem private_mono {K : A → Weight (J → Bool)} {r s : ℕ}
    (hK : Private r K) (hs : s ≤ r) : Private s K :=
  fun a b trace ht => hK a b trace (ht.trans hs)

theorem private_fiber (a : ℕ) (ha : 0 < a) (payload : A → Fin a → Bool) :
    Private (12 * a) (fun s => fiberWeight (BinaryCode.privateDecoder a ha) (payload s)) :=
  fun s t trace ht => privateDecoder_trace_masses a ha (payload s) (payload t) trace ht

end QueryComplexity.PrivateKernels

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

omit [Fintype A] [DecidableEq A] in
theorem productWeight_mass {K : Kernel T A J} (hK : Normalized K) (s : T → A) :
    (∑ x, productWeight K s x) = 1 := by
  unfold productWeight
  rw [← Fintype.prod_sum]
  exact Finset.prod_eq_one fun t _ => by simpa only [mass] using (hK t (s t)).2

omit [DecidableEq A] in
theorem score_leaf (f : (T → A) → Bool) (μ : Weight (T → A))
    {K : Kernel T A J} (hK : Normalized K) (b : Bool) :
    score f μ K (.leaf b) = labelMass f μ b := by
  unfold score labelMass mass restrict
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [DecisionTree.eval]
  by_cases hb : b = f s
  · simp [hb, productWeight_mass hK s]
  · simp [hb, Ne.symm hb]

noncomputable def conditioned (K : Kernel T A J) (t : T) (j : J) (b : Bool) : Kernel T A J :=
  Function.update K t (fun a => conditional (K t a) j b)

omit [Fintype T] [Fintype A] [DecidableEq A] in
theorem conditioned_normalized {K : Kernel T A J} (hK : Normalized K)
    (t : T) (j : J) (b : Bool) : Normalized (conditioned K t j b) := by
  intro u a
  by_cases hu : u = t
  · subst u
    simpa only [conditioned, Function.update_self] using
      And.intro (conditional_nonneg (hK t a).1 j b) (conditional_mass (hK t a).2 j b)
  · simpa only [conditioned, Function.update_of_ne hu] using hK u a

omit [Fintype A] [DecidableEq A] in
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

omit [DecidableEq A] in
theorem score_node (f : (T → A) → Bool) (μ : Weight (T → A))
    {K : Kernel T A J} (hK : Normalized K) (t : T) (j : J)
    (zero one : DecisionTree (T × J) Bool) (p : Bool → ℝ)
    (hp : ∀ s, μ s ≠ 0 → ∀ b, probability (K t (s t)) j b = p b) :
    score f μ K (.node (t, j) zero one) =
      p false * score f μ (conditioned K t j false) zero +
      p true * score f μ (conditioned K t j true) one := by
  simp only [score, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : μ s = 0
  · simp [hs]
  rw [← hp s hs false, ← hp s hs true]
  simp only [mul_left_comm (probability _ _ _), ← mul_add]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  simp only [← mul_assoc]
  rw [mul_comm (productWeight (conditioned K t j false) s x), conditioned_product hK,
    mul_comm (productWeight (conditioned K t j true) s x), conditioned_product hK]
  cases hb : x t j <;> simp [DecisionTree.eval, hb]

def restrictSymbol (μ : Weight (T → A)) (t : T) (a : A) : Weight (T → A) :=
  fun s => if s t = a then μ s else 0

omit [Fintype T] [DecidableEq T] [Fintype A] in
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
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [restrictSymbol, ite_mul]

omit [DecidableEq A] in
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
  simp only [Bool.false_eq_true, ↓reduceIte] at h0 h1
  exact (add_le_add h0 h1).trans_eq (by rw [← add_mul, hsum, one_mul])

end QueryComplexity.ProductKernels
