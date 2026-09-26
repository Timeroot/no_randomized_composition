import QueryComplexity.Randomized.Parallel
import QueryComplexity.CheatSheet.Basic

/-! Cost-certified certificate verification and the resulting randomized algorithm. -/

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
  simp only [coreOracle, RandomizedOracle.call_ofSubstitutions,
    FiniteRandomizedTree.probability_substitute]
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
  rw [comp_apply]
  refold_let input
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
        exact ha (by simpa only [decide_eq_true_eq, CertificateInput.AcceptsAt,
          certificateInputOfBits] using htarget)
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

namespace QueryComplexity.KleeneVerifier

variable {I S C : Type*} [Fintype I] [Fintype S] [Fintype C] {m : ℕ}

abbrev Core (m : ℕ) (S : Type*) := (Fin m × Fin m) × S
abbrev Witness (m : ℕ) := KleeneWitness (Fin m) (Fin m)

noncomputable def system (p : (S → Bool) → Option Bool) :
    CertificateSystem (Core m S → Bool) (Witness m) where
  valid x b witness := kleeneValid p (fun row col s => x ((row, col), s)) b witness
  compatible := kleeneValid_compatible p

def selected (witness : Witness m) (i : Fin m) : Fin m × Fin m :=
  match witness with
  | .inl select => (i, select i)
  | .inr row => (row, i)

def selectedValid (p : (S → Bool) → Option Bool) (b : Bool) (witness : Witness m)
    (data : Fin m → S → Bool) : Prop :=
  match b, witness with
  | true, .inl _ => ∀ i, p (data i) = some true
  | false, .inr _ => ∀ i, p (data i) = some false
  | _, _ => False

omit [Fintype S] in
theorem selectedValid_iff (p : (S → Bool) → Option Bool) (b : Bool) (witness : Witness m)
    (x : Core m S → Bool) :
    selectedValid p b witness (fun i s => x (selected witness i, s)) ↔
      (system p).valid x b witness := by
  cases b <;> cases witness <;> rfl

/-- Read the selected physical cell, decode its witnesses, then read exactly
one full seed block per witness index. No promise is made about the cell. -/
noncomputable def tree (p : (S → Bool) → Option Bool)
    (decode : CertificateDecoder I (Witness m) (C → Bool)) (address : I → Bool) :
    DecisionTree (CertificateCoordinates I (Core m S) C) Bool := by
  classical
  exact (DecisionTree.readCoordinates (fun c : C => Sum.inr (address, c))).bind fun cell =>
    let decoded := decode cell
    (DecisionTree.readCoordinates (fun coordinate : I × (Fin m × S) =>
      Sum.inl (coordinate.1, (selected (decoded.2 coordinate.1) coordinate.2.1, coordinate.2.2)))).mapOutput
      (fun data => decide (decoded.1 = true ∧ ∀ i,
        selectedValid p (address i) (decoded.2 i) (fun j s => data (i, j, s))))

theorem tree_depth_le (p : (S → Bool) → Option Bool)
    (decode : CertificateDecoder I (Witness m) (C → Bool)) (address : I → Bool) :
    (tree p decode address).depth ≤ Fintype.card C + Fintype.card I * m * Fintype.card S := by
  unfold tree
  apply DecisionTree.depth_bind_le_add
  · exact DecisionTree.depth_readCoordinates_le _
  · intro cell
    simp only [DecisionTree.depth_mapOutput]
    have h := DecisionTree.depth_readCoordinates_le
      (fun coordinate : I × (Fin m × S) =>
        (Sum.inl (coordinate.1, (selected ((decode cell).2 coordinate.1) coordinate.2.1,
          coordinate.2.2)) : CertificateCoordinates I (Core m S) C))
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_assoc] using h

theorem tree_correct (p : (S → Bool) → Option Bool)
    (decode : CertificateDecoder I (Witness m) (C → Bool)) (address : I → Bool)
    (x : CertificateCoordinates I (Core m S) C → Bool) :
    (tree p decode address).eval x = true ↔
      (certificateInputOfBits x).AcceptsAt (system p) decode address := by
  classical
  simp only [tree, DecisionTree.eval_bind, DecisionTree.eval_readCoordinates,
    DecisionTree.eval_mapOutput, decide_eq_true_eq]
  simp only [CertificateInput.AcceptsAt, certificateInputOfBits, system]
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  exact selectedValid_iff p (address i)
    ((decode ((certificateInputOfBits x).cells address)).2 i)
    (fun coordinate => x (.inl (i, coordinate)))

end QueryComplexity.KleeneVerifier
