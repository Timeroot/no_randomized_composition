import QueryComplexity.ApproxIndex.Basic
import ForMathlib.Probability.FiniteProbability

/-! Adaptive Hamming-ball activation estimates for the approximate-index seed. -/

open scoped BigOperators

namespace QueryComplexity.ApproxIndex

open FiniteProbability

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
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [sliceWeight_cons]
  cases a i <;> simp

def ballMass (radius : ℕ) (trace : AddressTrace k) (b : Fin k → Bool) : ℝ :=
  ∑ a, if distance a b ≤ radius then sliceWeight trace a else 0

/-- All conditional probabilities required by the adaptive simulation are
expressed as ratios of two finite sums over concrete address strings.
Inconsistent traces have zero mass and satisfy the bound automatically. -/
def BallSliceBound (radius budget : ℕ) (η : ℝ) : Prop :=
  ∀ trace : AddressTrace k, trace.length ≤ budget → ∀ b,
    ballMass radius trace b ≤ η * mass (sliceWeight trace)

def hitsBall (radius : ℕ) : DecisionTree (ApproxIndexCoordinates k) Bool →
    (Fin k → Bool) → Prop
  | .leaf _, _ => False
  | .node (.inl i) zero one, a => if a i then hitsBall radius one a else hitsBall radius zero a
  | .node (.inr (b, _)) zero _, a => distance a b ≤ radius ∨ hitsBall radius zero a

noncomputable instance (radius : ℕ) (tree : DecisionTree (ApproxIndexCoordinates k) Bool)
    (a : Fin k → Bool) : Decidable (hitsBall radius tree a) := Classical.propDecidable _

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
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [sliceWeight_cons]
  by_cases h : a i = true
  · simp [h]
  · have hf : a i = false := Bool.eq_false_of_not_eq_true h
    simp [hf]

theorem hitMass_table (radius : ℕ) (b : Fin k → Bool) (bit : Bool)
    (zero one : DecisionTree (ApproxIndexCoordinates k) Bool) (trace : AddressTrace k) :
    hitMass radius (DecisionTree.node (.inr (b, bit)) zero one) trace ≤
      ballMass radius trace b + hitMass radius zero trace := by
  simp only [hitMass, hitsBall, ballMass, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
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

end QueryComplexity.ApproxIndex
