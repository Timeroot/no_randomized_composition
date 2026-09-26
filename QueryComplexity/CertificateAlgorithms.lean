import QueryComplexity.ParallelAlgorithms
import QueryComplexity.Certificates

open scoped BigOperators

namespace QueryComplexity.CertificateAlgorithms

variable {I T C U Seed Witness : Type*}
  [Fintype I] [DecidableEq I] [Fintype U] [Fintype Seed]

noncomputable def exactBlock (g : BoolFn U) (coordinate : T) : DecisionTree (T × U) Bool :=
  (DecisionTree.readCoordinates (fun u : U => (coordinate, u))).mapOutput g

@[simp] theorem exactBlock_eval (g : BoolFn U) (coordinate : T) (x : T × U → Bool) :
    (exactBlock g coordinate).eval x = g (fun u => x (coordinate, u)) := by
  simp [exactBlock]

theorem exactBlock_depth_le (g : BoolFn U) (coordinate : T) :
    (exactBlock g coordinate).depth ≤ Fintype.card U := by
  simpa only [exactBlock, DecisionTree.depth_mapOutput] using
    DecisionTree.depth_readCoordinates_le (fun u : U => (coordinate, u))

def coreOracle (core : FiniteRandomizedTree Seed (T × U) Bool) :
    RandomizedOracle Seed I (CertificateCoordinates I T C × U) :=
  RandomizedOracle.ofSubstitutions core
    (fun i coordinate => .inr ((.inl (i, coordinate.1), coordinate.2), id))

omit [Fintype I] [DecidableEq I] [Fintype U] in
theorem coreOracle_probability (core : FiniteRandomizedTree Seed (T × U) Bool)
    (x : CertificateCoordinates I T C × U → Bool) (i : I) (event : Bool → Prop) :
    ((coreOracle core).call i).probability event x =
      core.probability event (fun coordinate => x (.inl (i, coordinate.1), coordinate.2)) := by
  change (core.substitute _).probability event x = _
  rw [FiniteRandomizedTree.probability_substitute]
  rfl

/-- The verifier is exact; only its selected address is randomized. -/
noncomputable def algorithm (g : BoolFn U) (core : FiniteRandomizedTree Seed (T × U) Bool)
    (verifier : (I → Bool) → DecisionTree (CertificateCoordinates I T C) Bool) :
    FiniteRandomizedTree (I → Seed) (CertificateCoordinates I T C × U) Bool :=
  (coreOracle core).parallel.bindDeterministic
    (fun address => (verifier address).expand (exactBlock g))

theorem algorithm_depthBound (g : BoolFn U) (core : FiniteRandomizedTree Seed (T × U) Bool)
    (verifier : (I → Bool) → DecisionTree (CertificateCoordinates I T C) Bool)
    {d v : ℕ} (hcore : core.DepthBound d) (hverifier : ∀ address, (verifier address).depth ≤ v) :
    (algorithm g core verifier).DepthBound (Fintype.card I * d + v * Fintype.card U) := by
  apply FiniteRandomizedTree.depthBound_bindDeterministic
  · apply RandomizedOracle.parallel_depthBound
    intro i seed
    exact (DecisionTree.depth_substitute_le _ _).trans (hcore seed)
  · intro address
    exact (DecisionTree.depth_expand_le _ _ (exactBlock_depth_le g)).trans
      (Nat.mul_le_mul_right _ (hverifier address))

theorem algorithm_error_le (S : CertificateSystem (T → Bool) Witness)
    (decode : CertificateDecoder I Witness (C → Bool)) (g : BoolFn U)
    (core : FiniteRandomizedTree Seed (T × U) Bool)
    (verifier : (I → Bool) → DecisionTree (CertificateCoordinates I T C) Bool)
    (hverifier : ∀ address input,
      (verifier address).eval input = true ↔
        (certificateInputOfBits input).AcceptsAt S decode address)
    (error : ℝ) (herror : 0 ≤ error)
    (hcore : ∀ input b, S.DefinedAt (fun t => g (fun u => input (t, u))) b →
      core.probability (fun output => output ≠ b) input ≤ error)
    (x : CertificateCoordinates I T C × U → Bool) :
    (algorithm g core verifier).probability
      (fun output => output ≠ comp (certificateBoolFn S decode) g x) x ≤ Fintype.card I * error := by
  classical
  let input := fun coordinate => g (fun u => x (coordinate, u))
  have heval (address : I → Bool) :
      ((verifier address).expand (exactBlock g)).eval x =
        decide ((certificateInputOfBits input).AcceptsAt S decode address) := by
    rw [DecisionTree.eval_expand]
    have h := hverifier address input
    simp only [exactBlock_eval]
    exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using h)
  unfold algorithm
  rw [FiniteRandomizedTree.probability_bindDeterministic]
  change (coreOracle core).parallel.probability
    (fun address => ((verifier address).expand (exactBlock g)).eval x ≠
      certificateBoolFn S decode input) x ≤ _
  cases hvalue : certificateBoolFn S decode input with
  | false =>
      have hno : ¬ ∃ address, (certificateInputOfBits input).AcceptsAt S decode address :=
        (CertificateInput.cheatSheet_eq_false_iff _ _ _).1 hvalue
      have hzero : (coreOracle core).parallel.probability
          (fun address => ((verifier address).expand (exactBlock g)).eval x ≠ false) x = 0 := by
        unfold FiniteRandomizedTree.probability
        apply Finset.sum_eq_zero
        intro seed _
        dsimp only
        rw [heval]
        have hn (address : I → Bool) :
            ¬ (certificateInputOfBits input).AcceptsAt S decode address := fun h => hno ⟨address, h⟩
        simp [hn]
      rw [hzero]
      exact mul_nonneg (Nat.cast_nonneg _) herror
  | true =>
      obtain ⟨target, htarget⟩ := (certificateBoolFn_eq_true_iff S decode input).1 hvalue
      change (certificateInputOfBits input).AcceptsAt S decode target at htarget
      have hbad : (coreOracle core).parallel.probability
          (fun address => ((verifier address).expand (exactBlock g)).eval x ≠ true) x ≤
          (coreOracle core).parallel.probability (fun address => ∃ i, address i ≠ target i) x := by
        apply FiniteRandomizedTree.probability_mono
        intro address ha
        by_contra hn
        have heq : address = target := by
          funext i
          by_contra hi
          exact hn ⟨i, hi⟩
        subst address
        rw [heval] at ha
        exact ha (by simp [htarget])
      refine hbad.trans ((FiniteRandomizedTree.probability_exists_le_sum _ _ _).trans ?_)
      calc
        _ ≤ ∑ _i : I, error := Finset.sum_le_sum fun i _ => by
          rw [FiniteRandomizedTree.probability_not,
            RandomizedOracle.probability_parallel_coordinate]
          rw [← FiniteRandomizedTree.probability_not, coreOracle_probability]
          apply hcore
          exact (certificateInputOfBits input).acceptsAt_definedAt S decode htarget i
        _ = _ := by simp [nsmul_eq_mul]

end QueryComplexity.CertificateAlgorithms
