import QueryComplexity.LowerBounds.DirectProduct
import QueryComplexity.DecisionTree.Cost
import ForMathlib.LinearAlgebra.BinaryCode
import ForMathlib.Probability.FiniteProbability
import QueryComplexity.Randomized.Algorithm

/-! Adaptive transcript privacy and its deterministic and randomized hybrid bounds. -/

open scoped BigOperators

namespace QueryComplexity.AdaptivePrivacy

open FiniteProbability DirectProduct

variable {T : Type*} [Fintype T] [DecidableEq T]

def traceWeight (μ : Weight (T → Bool)) : List (T × Bool) → Weight (T → Bool)
  | [] => μ
  | (j, b) :: rest => traceWeight (queried μ j b) rest

def accepts (μ : Weight (T → Bool)) (tree : DecisionTree T Bool) : ℝ :=
  score (fun _ => true) μ tree

/-- Equal masses for every short answer trace imply equal behavior for all
decision trees within that query budget. Repeated queries are permitted. -/
theorem accepts_eq_of_trace_masses (tree : DecisionTree T Bool) (d : ℕ)
    (μ ν : Weight (T → Bool))
    (hm : ∀ trace : List (T × Bool), trace.length ≤ d →
      mass (traceWeight μ trace) = mass (traceWeight ν trace))
    (hd : tree.depth ≤ d) : accepts μ tree = accepts ν tree := by
  induction tree generalizing d μ ν with
  | leaf b =>
    cases b
    · simp [accepts, score, DecisionTree.eval]
    · simpa [accepts, score, DecisionTree.eval, mass, traceWeight] using hm [] (by simp)
  | node j zero one ihz iho =>
    have hz : zero.depth ≤ d - 1 := by simp only [DecisionTree.depth] at hd; omega
    have ho : one.depth ≤ d - 1 := by simp only [DecisionTree.depth] at hd; omega
    have hdpos : 0 < d := by simp only [DecisionTree.depth] at hd; omega
    have hc (b : Bool) (trace : List (T × Bool)) (ht : trace.length ≤ d - 1) :
        mass (traceWeight (queried μ j b) trace) =
          mass (traceWeight (queried ν j b) trace) :=
      hm ((j, b) :: trace) (by simp; omega)
    unfold accepts
    rw [score_node, score_node]
    exact congrArg₂ (· + ·) (ihz (d - 1) _ _ (hc false) hz) (iho (d - 1) _ _ (hc true) ho)

/-- Stop before making query number `d+1`, preserving leaves already reached. -/
def stopAfter (fallback : Bool) : DecisionTree T Bool → ℕ → DecisionTree T Bool
  | .leaf b, _ => .leaf b
  | .node _ _ _, 0 => .leaf fallback
  | .node j zero one, d + 1 => .node j (stopAfter fallback zero d) (stopAfter fallback one d)

/-- Test whether execution would use more than `d` queries, using only `d`
queries itself. -/
def exceedsCost : DecisionTree T Bool → ℕ → DecisionTree T Bool
  | .leaf _, _ => .leaf false
  | .node _ _ _, 0 => .leaf true
  | .node j zero one, d + 1 => .node j (exceedsCost zero d) (exceedsCost one d)

omit [Fintype T] [DecidableEq T] in
theorem depth_stopAfter (tree : DecisionTree T Bool) (fallback : Bool) (d : ℕ) :
    (stopAfter fallback tree d).depth ≤ d := by
  induction d generalizing tree with
  | zero => cases tree <;> simp [stopAfter, DecisionTree.depth]
  | succ d ih =>
    cases tree with
    | leaf b => simp [stopAfter, DecisionTree.depth]
    | node j zero one =>
      simp only [stopAfter, DecisionTree.depth]
      have hz := ih zero
      have ho := ih one
      omega

omit [Fintype T] [DecidableEq T] in
theorem depth_exceedsCost (tree : DecisionTree T Bool) (d : ℕ) :
    (exceedsCost tree d).depth ≤ d := by
  induction d generalizing tree with
  | zero => cases tree <;> simp [exceedsCost, DecisionTree.depth]
  | succ d ih =>
    cases tree with
    | leaf b => simp [exceedsCost, DecisionTree.depth]
    | node j zero one =>
      simp only [exceedsCost, DecisionTree.depth]
      have hz := ih zero
      have ho := ih one
      omega

omit [Fintype T] [DecidableEq T] in
theorem eval_stopAfter (tree : DecisionTree T Bool) (fallback : Bool) (d : ℕ)
    (x : T → Bool) (hc : tree.queryCost x ≤ d) :
    (stopAfter fallback tree d).eval x = tree.eval x := by
  induction d generalizing tree with
  | zero =>
    cases tree with
    | leaf b => rfl
    | node j zero one => simp [DecisionTree.queryCost] at hc
  | succ d ih =>
    cases tree with
    | leaf b => rfl
    | node j zero one =>
      cases hx : x j
      · simp only [DecisionTree.queryCost, hx, Bool.false_eq_true, ↓reduceIte] at hc
        simpa [stopAfter, DecisionTree.eval, hx] using ih zero (by omega)
      · simp only [DecisionTree.queryCost, hx, ↓reduceIte] at hc
        simpa [stopAfter, DecisionTree.eval, hx] using ih one (by omega)

omit [Fintype T] [DecidableEq T] in
theorem eval_exceedsCost (tree : DecisionTree T Bool) (d : ℕ) (x : T → Bool) :
    (exceedsCost tree d).eval x = decide (d < tree.queryCost x) := by
  induction d generalizing tree with
  | zero => cases tree <;> simp [exceedsCost, DecisionTree.eval, DecisionTree.queryCost]
  | succ d ih =>
    cases tree with
    | leaf b => simp [exceedsCost, DecisionTree.eval, DecisionTree.queryCost]
    | node j zero one =>
      cases hx : x j <;>
        simp [exceedsCost, DecisionTree.eval, DecisionTree.queryCost, hx, ih] <;> omega

theorem accepts_nonnegative (tree : DecisionTree T Bool) {μ : Weight (T → Bool)}
    (hμ : Nonnegative μ) : 0 ≤ accepts μ tree := by
  refine Finset.sum_nonneg fun x _ => ?_
  dsimp [accepts, score]
  split_ifs
  · exact hμ x
  · exact le_rfl

theorem accepts_stopAfter_diff (tree : DecisionTree T Bool) (fallback : Bool) (d : ℕ)
    {μ : Weight (T → Bool)} (hμ : Nonnegative μ) :
    |accepts μ tree - accepts μ (stopAfter fallback tree d)| ≤ accepts μ (exceedsCost tree d) := by
  unfold accepts score
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  refine Finset.sum_le_sum fun x _ => ?_
  rw [eval_exceedsCost]
  by_cases hc : tree.queryCost x ≤ d
  · rw [eval_stopAfter tree fallback d x hc]
    simp [Nat.not_lt.mpr hc]
  · have hc' : d < tree.queryCost x := by omega
    simp only [hc', decide_true, ↓reduceIte]
    split_ifs <;> simp [abs_of_nonneg (hμ x), hμ x]

/-- Changing a hidden payload can affect the output only through executions
that exceed the indistinguishability budget. -/
theorem hybrid_bound (tree : DecisionTree T Bool) (d : ℕ)
    (μ ν : Weight (T → Bool)) (hμ : Nonnegative μ) (hν : Nonnegative ν)
    (hm : ∀ trace : List (T × Bool), trace.length ≤ d →
      mass (traceWeight μ trace) = mass (traceWeight ν trace)) :
    |accepts μ tree - accepts ν tree| ≤ 2 * accepts μ (exceedsCost tree d) := by
  have hstop := accepts_eq_of_trace_masses (stopAfter false tree d) d μ ν hm
    (depth_stopAfter tree false d)
  have hevent := accepts_eq_of_trace_masses (exceedsCost tree d) d μ ν hm
    (depth_exceedsCost tree d)
  have h₁ := accepts_stopAfter_diff tree false d hμ
  have h₂ := accepts_stopAfter_diff tree false d hν
  have ht := abs_add_le (accepts μ tree - accepts μ (stopAfter false tree d))
    (accepts ν (stopAfter false tree d) - accepts ν tree)
  rw [← hstop, sub_add_sub_cancel] at ht
  rw [abs_sub_comm (accepts μ (stopAfter false tree d))] at ht
  rw [← hstop, ← hevent] at h₂
  linarith

def Agrees (trace : List (T × Bool)) (x : T → Bool) : Prop :=
  ∀ p ∈ trace, x p.1 = p.2

instance agreesDecidable (trace : List (T × Bool)) (x : T → Bool) : Decidable (Agrees trace x) := by
  unfold Agrees
  infer_instance

omit [Fintype T] [DecidableEq T] in
theorem agrees_cons (trace : List (T × Bool)) (x : T → Bool) (j : T) (b : Bool) :
    Agrees ((j, b) :: trace) x ↔ x j = b ∧ Agrees trace x := by
  simp [Agrees]

theorem traceWeight_apply (μ : Weight (T → Bool)) (trace : List (T × Bool)) (x : T → Bool) :
    traceWeight μ trace x = if Agrees trace x then μ x else 0 := by
  classical
  induction trace generalizing μ with
  | nil => simp [traceWeight, Agrees]
  | cons p trace ih =>
    rcases p with ⟨j, b⟩
    rw [traceWeight, ih]
    by_cases hj : x j = b <;> by_cases ht : Agrees trace x <;>
      simp [queried, restrict, agrees_cons, hj, ht]

noncomputable def fiberWeight {W : Type*} (H : (T → Bool) → W) (w : W) : Weight (T → Bool) := by
  classical
  exact fun x => if H x = w then 1 / (Nat.card {x : T → Bool // H x = w} : ℝ) else 0

omit [Fintype T] [DecidableEq T] in
theorem fiberWeight_nonnegative {W : Type*} (H : (T → Bool) → W) (w : W) :
    Nonnegative (fiberWeight H w) := by
  classical
  intro x
  unfold fiberWeight
  split_ifs <;> positivity

theorem sum_uniform_indicator {X : Type*} [Fintype X] (P : X → Prop) [DecidablePred P] (d : ℝ) :
    (∑ x, if P x then 1 / d else 0) = (Nat.card {x : X // P x} : ℝ) / d := by
  classical
  calc
    (∑ x, if P x then 1 / d else 0) = (∑ x, if P x then (1 : ℝ) else 0) / d := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> simp
    _ = _ := by simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem mass_fiberWeight {W : Type*} (H : (T → Bool) → W)
    (hH : Function.Surjective H) (w : W) : mass (fiberWeight H w) = 1 := by
  classical
  obtain ⟨x, hx⟩ := hH w
  letI : Nonempty {x : T → Bool // H x = w} := ⟨⟨x, hx⟩⟩
  unfold mass fiberWeight
  rw [sum_uniform_indicator]
  exact div_self (by exact_mod_cast (Nat.card_pos (α := {x : T → Bool // H x = w})).ne')

theorem trace_mass_fiberWeight {W : Type*} (H : (T → Bool) → W)
    (w : W) (trace : List (T × Bool)) :
    mass (traceWeight (fiberWeight H w) trace) =
      (Nat.card {x : T → Bool // H x = w ∧ Agrees trace x} : ℝ) /
        (Nat.card {x : T → Bool // H x = w} : ℝ) := by
  classical
  unfold mass
  simp_rw [traceWeight_apply, fiberWeight]
  calc
    (∑ x : T → Bool, if Agrees trace x then
        (if H x = w then 1 / (Nat.card {x : T → Bool // H x = w} : ℝ) else 0) else 0) =
      ∑ x : T → Bool, if H x = w ∧ Agrees trace x then
        1 / (Nat.card {x : T → Bool // H x = w} : ℝ) else 0 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> tauto
    _ = _ := sum_uniform_indicator _ _

def observedCoordinates (trace : List (T × Bool)) : Finset T :=
  (trace.map Prod.fst).toFinset

omit [Fintype T] in
theorem observedCoordinates_card_le (trace : List (T × Bool)) :
    (observedCoordinates trace).card ≤ trace.length := by
  exact (List.toFinset_card_le _).trans (by simp)

omit [Fintype T] in
theorem agrees_iff_restriction (trace : List (T × Bool)) (base : T → Bool)
    (hbase : Agrees trace base) (x : T → Bool) :
    Agrees trace x ↔ Cosets.restrictCoordinates (observedCoordinates trace) x =
      Cosets.restrictCoordinates (observedCoordinates trace) base := by
  classical
  constructor
  · intro hx
    funext j
    obtain ⟨p, hp, hpj⟩ := List.mem_map.mp (List.mem_toFinset.mp j.2)
    simp only [Cosets.restrictCoordinates, LinearMap.coe_mk, AddHom.coe_mk,
      ← hpj, hx p hp, hbase p hp]
  · intro hx p hp
    have hj : p.1 ∈ observedCoordinates trace := by
      apply List.mem_toFinset.mpr
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    have he := congrArg (fun f => f ⟨p.1, hj⟩) hx
    exact he.trans (hbase p hp)

theorem privateDecoder_trace_masses (a : ℕ) (ha : 0 < a)
    (u v : Fin a → Bool) (trace : List (Fin (36 * a) × Bool)) (ht : trace.length ≤ 12 * a) :
    mass (traceWeight (fiberWeight (BinaryCode.privateDecoder a ha) u) trace) =
      mass (traceWeight (fiberWeight (BinaryCode.privateDecoder a ha) v) trace) := by
  classical
  by_cases hc : ∃ x, Agrees trace x
  · obtain ⟨base, hbase⟩ := hc
    have hs : (observedCoordinates trace).card ≤ 12 * a :=
      (observedCoordinates_card_le trace).trans ht
    have he (w : Fin a → Bool) :
        Nat.card {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = w ∧ Agrees trace x} =
        Nat.card {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = w ∧
          Cosets.restrictCoordinates (observedCoordinates trace) x =
          Cosets.restrictCoordinates (observedCoordinates trace) base} := by
      apply Nat.card_congr
      exact Equiv.subtypeEquivRight (fun x => and_congr_right (fun _ => agrees_iff_restriction trace base hbase x))
    simp_rw [trace_mass_fiberWeight, he]
    rw [BinaryCode.privateDecoder_uniform a ha _ hs,
      BinaryCode.privateDecoder_uniform a ha _ hs]
  · have hz (w : Fin a → Bool) :
        mass (traceWeight (fiberWeight (BinaryCode.privateDecoder a ha) w) trace) = 0 := by
      unfold mass
      apply Finset.sum_eq_zero
      intro x _
      rw [traceWeight_apply, if_neg (fun h => hc ⟨x, h⟩)]
    rw [hz, hz]

theorem privateDecoder_hybrid (a : ℕ) (ha : 0 < a)
    (u v : Fin a → Bool) (tree : DecisionTree (Fin (36 * a)) Bool) :
    |accepts (fiberWeight (BinaryCode.privateDecoder a ha) u) tree -
        accepts (fiberWeight (BinaryCode.privateDecoder a ha) v) tree| ≤
      2 * accepts (fiberWeight (BinaryCode.privateDecoder a ha) u) (exceedsCost tree (12 * a)) :=
  hybrid_bound tree (12 * a) _ _ (fiberWeight_nonnegative _ _) (fiberWeight_nonnegative _ _)
    (privateDecoder_trace_masses a ha u v)

theorem fiber_accepts_count {W : Type*} (H : (T → Bool) → W)
    (w : W) (tree : DecisionTree T Bool) :
    accepts (fiberWeight H w) tree =
      (Nat.card {x : T → Bool // H x = w ∧ tree.eval x = true} : ℝ) /
        (Nat.card {x : T → Bool // H x = w} : ℝ) := by
  classical
  unfold accepts score fiberWeight
  calc
    (∑ x, if tree.eval x = true then
        (if H x = w then 1 / (Nat.card {x : T → Bool // H x = w} : ℝ) else 0) else 0) =
        ∑ x, if H x = w ∧ tree.eval x = true then
          1 / (Nat.card {x : T → Bool // H x = w} : ℝ) else 0 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> tauto
    _ = _ := sum_uniform_indicator _ _

theorem fiber_accepts_eq_average {W : Type*} [DecidableEq W] (H : (T → Bool) → W)
    (w : W) (tree : DecisionTree T Bool) :
    accepts (fiberWeight H w) tree =
      average (fun x : {x : T → Bool // H x = w} =>
        if tree.eval x.1 = true then (1 : ℝ) else 0) := by
  classical
  rw [fiber_accepts_count]
  unfold average uniformWeight
  simp only [mul_ite, mul_one, mul_zero]
  have he : Nat.card {z : {x : T → Bool // H x = w} // tree.eval z.1 = true} =
      Nat.card {x : T → Bool // H x = w ∧ tree.eval x = true} := by
    apply Nat.card_congr
    exact {
      toFun := fun z => ⟨z.1.1, z.1.2, z.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← one_div, sum_uniform_indicator, he, Nat.card_eq_fintype_card]
  simp only [Nat.card_eq_fintype_card]

theorem privateDecoder_average_hybrid (a : ℕ) (ha : 0 < a)
    (u v : Fin a → Bool) (tree : DecisionTree (Fin (36 * a)) Bool) :
    |average (fun x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = u} =>
        if tree.eval x.1 = true then (1 : ℝ) else 0) -
      average (fun x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = v} =>
        if tree.eval x.1 = true then (1 : ℝ) else 0)| ≤
      2 * average (fun x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = u} =>
        if 12 * a < tree.queryCost x.1 then (1 : ℝ) else 0) := by
  simpa only [fiber_accepts_eq_average, eval_exceedsCost, decide_eq_true_eq] using
    privateDecoder_hybrid a ha u v tree

end QueryComplexity.AdaptivePrivacy

open scoped BigOperators

namespace QueryComplexity.RandomizedPrivacy

open FiniteProbability AdaptivePrivacy

theorem probability_weighted_sum {Seed T Output : Type*} [Fintype Seed]
    (A : FiniteRandomizedTree Seed T Output) (event : Output → Prop) [DecidablePred event] (x : T → Bool) :
    A.probability event x =
      ∑ s, A.weight s * (if event ((A.tree s).eval x) then (1 : ℝ) else 0) := by
  classical
  unfold FiniteRandomizedTree.probability
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp_all

theorem privateDecoder_heavy_probability {Seed : Type*} [Fintype Seed]
    (a : ℕ) (ha : 0 < a) (u v : Fin a → Bool)
    (A : FiniteRandomizedTree Seed (Fin (36 * a)) Bool)
    (hzero : ∀ x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = u},
      A.probability (fun b => b = true) x.1 ≤ 1 / 3)
    (hone : ∀ x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = v},
      2 / 3 ≤ A.probability (fun b => b = true) x.1) :
    (1 : ℝ) / 6 ≤ ∑ s, A.weight s *
      average (fun x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = u} =>
        if 12 * a < (A.tree s).queryCost x.1 then (1 : ℝ) else 0) := by
  classical
  have hnonempty (w : Fin a → Bool) :
      Nonempty {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = w} := by
    obtain ⟨x, hx⟩ := BinaryCode.privateDecoder_surjective a ha w
    exact ⟨⟨x, hx⟩⟩
  letI := hnonempty u
  letI := hnonempty v
  have hneg : average (fun x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = u} =>
      A.probability (fun b => b = true) x.1) ≤ 1 / 3 := by
    exact (average_le hzero).trans_eq (average_const _)
  have hpos : 2 / 3 ≤ average (fun x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = v} =>
      A.probability (fun b => b = true) x.1) := by
    exact (average_const _).symm.trans_le (average_le hone)
  have he (w : Fin a → Bool) :
      average (fun x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = w} =>
        A.probability (fun b => b = true) x.1) =
      ∑ s, A.weight s * average
        (fun x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = w} =>
          if (A.tree s).eval x.1 = true then (1 : ℝ) else 0) := by
    simp_rw [probability_weighted_sum, average_sum, average_mul]
  have hh (s : Seed) := privateDecoder_average_hybrid a ha u v (A.tree s)
  have hd (s : Seed) :
      average (fun x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = v} =>
        if (A.tree s).eval x.1 = true then (1 : ℝ) else 0) -
      average (fun x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = u} =>
        if (A.tree s).eval x.1 = true then (1 : ℝ) else 0) ≤
      2 * average (fun x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = u} =>
        if 12 * a < (A.tree s).queryCost x.1 then (1 : ℝ) else 0) := by
    have h := hh s
    rw [abs_sub_comm] at h
    exact (le_abs_self _).trans h
  have hw := Finset.sum_le_sum (s := Finset.univ)
    (fun s _ => mul_le_mul_of_nonneg_left (hd s) (A.weight_nonneg s))
  simp only [mul_sub, Finset.sum_sub_distrib] at hw
  rw [he u] at hneg
  rw [he v] at hpos
  have hscale : (∑ s, A.weight s * (2 *
      average (fun x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = u} =>
        if 12 * a < (A.tree s).queryCost x.1 then (1 : ℝ) else 0))) =
      2 * ∑ s, A.weight s * average
        (fun x : {x : Fin (36 * a) → Bool // BinaryCode.privateDecoder a ha x = u} =>
          if 12 * a < (A.tree s).queryCost x.1 then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [hscale] at hw
  linarith

end QueryComplexity.RandomizedPrivacy
