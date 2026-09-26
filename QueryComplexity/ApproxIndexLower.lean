import QueryComplexity.ApproxIndex
import QueryComplexity.DirectProduct

/-! A hard distribution for ApproxIndex. The only remaining combinatorial
hypothesis in the principal seed bound is an explicit Hamming-ball bound on
address subcubes. The query tree, adaptive erasure simulation, and finite
probability calculations are concrete. -/

open scoped BigOperators

namespace QueryComplexity.ApproxIndex

open FiniteProbability DirectProduct

variable {k : ℕ}

abbrev AddressTrace (k : ℕ) := List (Fin k × Bool)

def traceMatches (trace : AddressTrace k) (a : Fin k → Bool) : Prop :=
  ∀ p ∈ trace, a p.1 = p.2

instance (trace : AddressTrace k) (a : Fin k → Bool) : Decidable (traceMatches trace a) :=
  inferInstanceAs (Decidable (∀ p ∈ trace, a p.1 = p.2))

def sliceWeight (trace : AddressTrace k) : Weight (Fin k → Bool) :=
  fun a => if traceMatches trace a then 1 else 0

theorem sliceWeight_nonnegative (trace : AddressTrace k) : Nonnegative (sliceWeight trace) := by
  intro a
  simp only [sliceWeight]
  split_ifs <;> norm_num

@[simp] theorem sliceWeight_nil (a : Fin k → Bool) : sliceWeight [] a = 1 := by
  simp [sliceWeight, traceMatches]

theorem sliceWeight_cons (trace : AddressTrace k) (i : Fin k) (b : Bool)
    (a : Fin k → Bool) :
    sliceWeight ((i, b) :: trace) a = if a i = b then sliceWeight trace a else 0 := by
  simp only [sliceWeight, traceMatches, List.mem_cons, forall_eq_or_imp]
  by_cases hi : a i = b <;> simp [hi]

theorem sliceWeight_split (trace : AddressTrace k) (i : Fin k) :
    mass (sliceWeight ((i, false) :: trace)) +
      mass (sliceWeight ((i, true) :: trace)) = mass (sliceWeight trace) := by
  simp only [mass, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [sliceWeight_cons, sliceWeight_cons]
  cases h : a i <;> simp [h]

def ballMass (radius : ℕ) (trace : AddressTrace k) (b : Fin k → Bool) : ℝ :=
  ∑ a, if distance a b ≤ radius then sliceWeight trace a else 0

/-- All conditional probabilities required by the adaptive simulation are
expressed as ratios of two finite sums over concrete address strings.
Inconsistent traces have zero mass and satisfy the bound automatically. -/
def BallSliceBound (radius budget : ℕ) (η : ℝ) : Prop :=
  ∀ trace : AddressTrace k, trace.length ≤ budget → ∀ b,
    ballMass radius trace b ≤ η * mass (sliceWeight trace)

/-- The fake input answers address queries truthfully and all table queries
with `false`, independently of the hidden output bit. -/
def erasedInput (a : Fin k → Bool) : ApproxIndexCoordinates k → Bool
  | .inl i => a i
  | .inr _ => false

def hitsBall (radius : ℕ) : DecisionTree (ApproxIndexCoordinates k) Bool →
    (Fin k → Bool) → Prop
  | .leaf _, _ => False
  | .node (.inl i) zero one, a => if a i then hitsBall radius one a else hitsBall radius zero a
  | .node (.inr (b, _)) zero _, a => distance a b ≤ radius ∨ hitsBall radius zero a

noncomputable instance (radius : ℕ) (tree : DecisionTree (ApproxIndexCoordinates k) Bool)
    (a : Fin k → Bool) : Decidable (hitsBall radius tree a) := Classical.propDecidable _

theorem eval_eq_erased_of_no_hit (radius : ℕ)
    (tree : DecisionTree (ApproxIndexCoordinates k) Bool) (a : Fin k → Bool) (z : Bool)
    (h : ¬ hitsBall radius tree a) :
    tree.eval (encode radius a z) = tree.eval (erasedInput a) := by
  induction tree with
  | leaf b => rfl
  | node coordinate zero one ihz iho =>
    cases coordinate with
    | inl i =>
      by_cases hi : a i = true
      · simp only [hitsBall, hi, if_true] at h
        simpa only [DecisionTree.eval, encode, erasedInput, hi, if_true] using iho h
      · have hi' : a i = false := Bool.eq_false_of_not_eq_true hi
        simp only [hitsBall, hi', Bool.false_eq_true, if_false] at h
        simpa only [DecisionTree.eval, encode, erasedInput, hi', Bool.false_eq_true, if_false]
          using ihz h
    | inr p =>
      rcases p with ⟨b, bit⟩
      have hb : ¬ distance a b ≤ radius := fun hb => h (Or.inl hb)
      have hz : ¬ hitsBall radius zero a := fun hz => h (Or.inr hz)
      cases bit <;>
        simpa [DecisionTree.eval, encode, erasedInput, hb] using ihz hz

noncomputable def hitMass (radius : ℕ) (tree : DecisionTree (ApproxIndexCoordinates k) Bool)
    (trace : AddressTrace k) : ℝ :=
  ∑ a, if hitsBall radius tree a then sliceWeight trace a else 0

@[simp] theorem hitMass_leaf (radius : ℕ) (b : Bool) (trace : AddressTrace k) :
    hitMass radius (.leaf b) trace = 0 := by
  simp [hitMass, hitsBall]

theorem hitMass_address (radius : ℕ) (i : Fin k)
    (zero one : DecisionTree (ApproxIndexCoordinates k) Bool) (trace : AddressTrace k) :
    hitMass radius (DecisionTree.node (.inl i) zero one) trace =
      hitMass radius zero ((i, false) :: trace) + hitMass radius one ((i, true) :: trace) := by
  simp only [hitMass, hitsBall, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [sliceWeight_cons, sliceWeight_cons]
  by_cases h : a i = true
  · simp [h]
  · have hf : a i = false := Bool.eq_false_of_not_eq_true h
    simp [hf]

theorem hitMass_table (radius : ℕ) (b : Fin k → Bool) (bit : Bool)
    (zero one : DecisionTree (ApproxIndexCoordinates k) Bool) (trace : AddressTrace k) :
    hitMass radius (DecisionTree.node (.inr (b, bit)) zero one) trace ≤
      ballMass radius trace b + hitMass radius zero trace := by
  simp only [hitMass, hitsBall, ballMass, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  by_cases hb : distance a b ≤ radius <;> by_cases hz : hitsBall radius zero a <;>
    simp [hb, hz, sliceWeight_nonnegative trace a]

theorem hitMass_le (radius budget : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (hball : @BallSliceBound k radius budget η)
    (tree : DecisionTree (ApproxIndexCoordinates k) Bool) (trace : AddressTrace k)
    (hbudget : trace.length + tree.depth ≤ budget) :
    hitMass radius tree trace ≤ (tree.depth : ℝ) * η * mass (sliceWeight trace) := by
  induction tree generalizing trace with
  | leaf b => simp [DecisionTree.depth]
  | node coordinate zero one ihz iho =>
    have hz : zero.depth ≤ (DecisionTree.node coordinate zero one).depth := by
      simp only [DecisionTree.depth]
      omega
    have ho : one.depth ≤ (DecisionTree.node coordinate zero one).depth := by
      simp only [DecisionTree.depth]
      omega
    cases coordinate with
    | inl i =>
      have hzt : ((i, false) :: trace).length + zero.depth ≤ budget := by
        simp only [List.length_cons, DecisionTree.depth] at *
        omega
      have hot : ((i, true) :: trace).length + one.depth ≤ budget := by
        simp only [List.length_cons, DecisionTree.depth] at *
        omega
      rw [hitMass_address]
      calc
        _ ≤ (zero.depth : ℝ) * η * mass (sliceWeight ((i, false) :: trace)) +
            (one.depth : ℝ) * η * mass (sliceWeight ((i, true) :: trace)) :=
          add_le_add (ihz _ hzt) (iho _ hot)
        _ ≤ ((DecisionTree.node (.inl i) zero one).depth : ℝ) * η *
            mass (sliceWeight ((i, false) :: trace)) +
            ((DecisionTree.node (.inl i) zero one).depth : ℝ) * η *
            mass (sliceWeight ((i, true) :: trace)) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hz) hη)
              (mass_nonnegative (sliceWeight_nonnegative _))
          · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast ho) hη)
              (mass_nonnegative (sliceWeight_nonnegative _))
        _ = _ := by rw [← mul_add, sliceWeight_split]
    | inr p =>
      rcases p with ⟨b, bit⟩
      have ht : trace.length ≤ budget := by omega
      have hzt : trace.length + zero.depth ≤ budget := by omega
      have hz' : (1 + zero.depth : ℕ) ≤ (DecisionTree.node (.inr (b, bit)) zero one).depth := by
        simp only [DecisionTree.depth]
        omega
      calc
        _ ≤ ballMass radius trace b + hitMass radius zero trace :=
          hitMass_table radius b bit zero one trace
        _ ≤ η * mass (sliceWeight trace) + (zero.depth : ℝ) * η * mass (sliceWeight trace) :=
          add_le_add (hball trace ht b) (ihz trace hzt)
        _ = ((1 + zero.depth : ℕ) : ℝ) * η * mass (sliceWeight trace) := by
          push_cast
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hz') hη)
          (mass_nonnegative (sliceWeight_nonnegative _))

theorem correctPair_le (radius : ℕ)
    (tree : DecisionTree (ApproxIndexCoordinates k) Bool) (a : Fin k → Bool) :
    (∑ z : Bool, if tree.eval (encode radius a z) = z then (1 : ℝ) else 0) ≤
      1 + if hitsBall radius tree a then 1 else 0 := by
  by_cases hh : hitsBall radius tree a
  · simp only [hh, if_true, Fintype.sum_bool]
    split_ifs <;> norm_num
  · simp only [hh, if_false, add_zero, Fintype.sum_bool]
    rw [eval_eq_erased_of_no_hit radius tree a true hh,
      eval_eq_erased_of_no_hit radius tree a false hh]
    cases tree.eval (erasedInput a) <;> norm_num

theorem correctCount_le (radius budget : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (hball : @BallSliceBound k radius budget η)
    (tree : DecisionTree (ApproxIndexCoordinates k) Bool) (hdepth : tree.depth ≤ budget) :
    (∑ a : Fin k → Bool, ∑ z : Bool,
      if tree.eval (encode radius a z) = z then (1 : ℝ) else 0) ≤
      (1 + (budget : ℝ) * η) * (2 : ℝ) ^ k := by
  have hm : mass (sliceWeight ([] : AddressTrace k)) = (2 : ℝ) ^ k := by
    simp [mass]
  have hh := hitMass_le radius budget η hη hball tree [] (by simpa using hdepth)
  rw [hm] at hh
  calc
    _ ≤ ∑ a : (Fin k → Bool), ((1 : ℝ) + if hitsBall radius tree a then 1 else 0) :=
      Finset.sum_le_sum fun a _ => correctPair_le radius tree a
    _ = (2 : ℝ) ^ k + hitMass radius tree [] := by
      simp [Finset.sum_add_distrib, hitMass]
    _ ≤ (2 : ℝ) ^ k + (tree.depth : ℝ) * η * (2 : ℝ) ^ k := add_le_add (le_refl _) hh
    _ ≤ (2 : ℝ) ^ k + (budget : ℝ) * η * (2 : ℝ) ^ k := by
      apply add_le_add (le_refl _)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hdepth) hη) (by positivity)
    _ = _ := by ring

/-- Uniform address and a uniform hidden output bit, encoded as valid seed
inputs with `false` values at all erased entries. -/
noncomputable def hardWeight (k radius : ℕ) : Weight (ApproxIndexCoordinates k → Bool) :=
  pushforward (uniformWeight ((Fin k → Bool) × Bool))
    (fun p => encode radius p.1 p.2)

theorem hardWeight_nonnegative (k radius : ℕ) : Nonnegative (hardWeight k radius) :=
  pushforward_nonnegative (uniformWeight_nonnegative _) _

theorem mass_hardWeight (k radius : ℕ) : mass (hardWeight k radius) = 1 := by
  rw [hardWeight, mass_pushforward, mass_uniformWeight]

theorem hardWeight_eq_zero_of_invalid (radius : ℕ) (x : ApproxIndexCoordinates k → Bool)
    (h : ∀ z, ¬ Valid radius x z) : hardWeight k radius x = 0 := by
  classical
  unfold hardWeight pushforward
  apply Finset.sum_eq_zero
  intro p _
  have he : encode radius p.1 p.2 ≠ x := by
    intro he
    apply h p.2
    rw [← he]
    exact valid_encode radius p.1 p.2
  simp [he]

theorem hardWeight_supported (radius : ℕ) (x : ApproxIndexCoordinates k → Bool)
    (h : hardWeight k radius x ≠ 0) : ∃ z, Valid radius x z := by
  classical
  by_contra hn
  apply h
  apply hardWeight_eq_zero_of_invalid
  simpa only [not_exists] using hn

theorem hardWeight_score (radius : ℕ) (tree : DecisionTree (ApproxIndexCoordinates k) Bool) :
    score extension (hardWeight k radius) tree =
      (∑ a : Fin k → Bool, ∑ z : Bool,
        if tree.eval (encode radius a z) = z then (1 : ℝ) else 0) /
        (2 * (2 : ℝ) ^ k) := by
  have hp := sum_pushforward_mul (uniformWeight ((Fin k → Bool) × Bool))
    (fun p => encode radius p.1 p.2)
    (fun x => if tree.eval x = extension x then (1 : ℝ) else 0)
  have he (a : Fin k → Bool) (z : Bool) : extension (encode radius a z) = z :=
    extension_correct radius _ _ (value_encode radius a z)
  have hs : score extension (hardWeight k radius) tree =
      ∑ x, hardWeight k radius x *
        (if tree.eval x = extension x then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  rw [hs]
  change (∑ x, pushforward (uniformWeight ((Fin k → Bool) × Bool))
    (fun p => encode radius p.1 p.2) x * _) = _
  rw [hp, Fintype.sum_prod_type]
  simp only [he, uniformWeight, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  simp_rw [← Finset.mul_sum]
  simp only [div_eq_mul_inv, mul_comm]

theorem hardWeight_score_le (radius budget : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (hball : @BallSliceBound k radius budget η)
    (tree : DecisionTree (ApproxIndexCoordinates k) Bool) (hdepth : tree.depth ≤ budget) :
    score extension (hardWeight k radius) tree ≤ (1 + (budget : ℝ) * η) / 2 := by
  rw [hardWeight_score]
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  calc
    _ ≤ ((1 + (budget : ℝ) * η) * (2 : ℝ) ^ k) / (2 * (2 : ℝ) ^ k) :=
      div_le_div_of_nonneg_right (correctCount_le radius budget η hη hball tree hdepth)
        (by positivity)
    _ = _ := by field_simp

/-- This is an actual randomized query lower bound for the deterministic
extension, proved from an explicit distribution supported on valid seeds. -/
theorem R_extension_gt_of_ballSliceBound (radius budget : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (hball : @BallSliceBound k radius budget η) (hsmall : (budget : ℝ) * η < 1 / 3) :
    budget < R (@extension k) := by
  exact R_gt_of_hard_distribution extension budget (hardWeight k radius)
    (hardWeight_nonnegative k radius) (mass_hardWeight k radius)
    ((1 + (budget : ℝ) * η) / 2) (by linarith)
    (fun tree hdepth => hardWeight_score_le radius budget η hη hball tree hdepth)

end QueryComplexity.ApproxIndex
