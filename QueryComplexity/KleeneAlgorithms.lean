import QueryComplexity.RobustAndOr
import QueryComplexity.Certificates

namespace QueryComplexity.KleeneAlgorithms

variable {Seed S U : Type*} [Fintype Seed] {m : ℕ}

def oracle (seedAlgorithm : FiniteRandomizedTree Seed (S × U) Bool) :
    RandomizedOracle Seed (Fin m × Fin m) (((Fin m × Fin m) × S) × U) :=
  RandomizedOracle.ofSubstitutions seedAlgorithm
    (fun pair coordinate => .inr (((pair, coordinate.1), coordinate.2), id))

theorem oracle_probability (seedAlgorithm : FiniteRandomizedTree Seed (S × U) Bool)
    (x : ((Fin m × Fin m) × S) × U → Bool) (pair : Fin m × Fin m) (event : Bool → Prop) :
    ((oracle seedAlgorithm).call pair).probability event x =
      seedAlgorithm.probability event (fun coordinate => x ((pair, coordinate.1), coordinate.2)) := by
  change (seedAlgorithm.substitute _).probability event x = _
  rw [FiniteRandomizedTree.probability_substitute]
  rfl

noncomputable def algorithm (seedAlgorithm : FiniteRandomizedTree Seed (S × U) Bool) :
    FiniteRandomizedTree
      (RandomizedOracle.Seeds (RandomizedOracle.Seeds Seed (3000 * m + 1)) (3000 * m + 1))
      (((Fin m × Fin m) × S) × U) Bool :=
  RobustAndOr.robust (oracle seedAlgorithm)

theorem algorithm_depthBound (seedAlgorithm : FiniteRandomizedTree Seed (S × U) Bool)
    (hm : 0 < m) {cost : ℕ} (hcost : seedAlgorithm.DepthBound cost) :
    (algorithm (m := m) seedAlgorithm).DepthBound (3001 ^ 2 * m ^ 2 * cost) := by
  apply RobustAndOr.robust_depthBound _ hm
  intro pair seed
  exact (DecisionTree.depth_substitute_le _ _).trans (hcost seed)

theorem algorithm_error (p : (S → Bool) → Option Bool) (g : BoolFn U)
    (seedAlgorithm : FiniteRandomizedTree Seed (S × U) Bool) (hm : 0 < m)
    (hseed : ∀ input b, p (fun s => g (fun u => input (s, u))) = some b →
      seedAlgorithm.probability (fun output => output ≠ b) input ≤ 1 / 3)
    (x : ((Fin m × Fin m) × S) × U → Bool) (b : Bool)
    (hw : ∃ w, kleeneValid p (fun row col s => g (fun u => x (((row, col), s), u))) b w) :
    (algorithm seedAlgorithm).probability (fun output => output ≠ b) x ≤ 1 / 100 := by
  obtain ⟨w, hw⟩ := hw
  cases b with
  | false =>
      cases w with
      | inl select => exact False.elim hw
      | inr row =>
          have h := RobustAndOr.robust_zero (oracle seedAlgorithm) hm x (by
            refine ⟨row, fun col => ?_⟩
            change ((oracle seedAlgorithm).call (row, col)).probability _ x ≤ _
            rw [oracle_probability]
            have he := hseed (fun coordinate => x (((row, col), coordinate.1), coordinate.2)) false (hw col)
            simpa only [Bool.not_eq_false] using he)
          simpa only [Bool.not_eq_false] using h
  | true =>
      cases w with
      | inr row => exact False.elim hw
      | inl select =>
          have h := RobustAndOr.robust_one (oracle seedAlgorithm) hm x (by
            intro row
            refine ⟨select row, ?_⟩
            change 2 / 3 ≤ ((oracle seedAlgorithm).call (row, select row)).probability _ x
            rw [oracle_probability]
            have he := hseed (fun coordinate => x (((row, select row), coordinate.1), coordinate.2)) true (hw row)
            simp only [Bool.not_eq_true] at he
            rw [FiniteRandomizedTree.probability_false] at he
            linarith)
          simpa only [Bool.not_eq_true] using h

end QueryComplexity.KleeneAlgorithms
