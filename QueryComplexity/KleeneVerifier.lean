import QueryComplexity.CertificateAlgorithms

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
  change (_ ∧ ∀ i, selectedValid p (address i) _ _) ↔ (_ ∧ ∀ i, (system p).valid _ _ _)
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  exact selectedValid_iff p (address i)
    ((decode ((certificateInputOfBits x).cells address)).2 i)
    (fun coordinate => x (.inl (i, coordinate)))

end QueryComplexity.KleeneVerifier
