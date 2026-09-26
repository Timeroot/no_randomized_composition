import QueryComplexity.DecisionTree.QueryList
import QueryComplexity.CheatSheet.Basic

/-! Restricting a certificate query tree to one physical cell, and extracting
a heavy-cell list while fixing the entire cell array. -/

namespace QueryComplexity.CellProjection

open DecisionTree

universe u v w z

variable {I : Type u} {T : Type v} {C : Type w} {Output : Type z}
variable [Fintype I] [DecidableEq I]

def cellOwner : CertificateCoordinates I T C → Option (I → Bool)
  | .inl _ => none
  | .inr (address, _) => some address

def cellSubstitution (cores : I → T → Bool) (cells : (I → Bool) → C → Bool)
    (target : I → Bool) : BitSubstitution C (CertificateCoordinates I T C)
  | .inl (i, t) => .inl (cores i t)
  | .inr (address, c) => if address = target then .inr (c, id) else .inl (cells address c)

omit [DecidableEq I] in
@[simp] theorem cellSubstitution_eval (cores : I → T → Bool)
    (cells : (I → Bool) → C → Bool) (target : I → Bool) (word : C → Bool) :
    (cellSubstitution cores cells target).eval word =
      certificateBitsOfInput ⟨cores, Function.update cells target word⟩ := by
  funext coord
  cases coord with
  | inl p => cases p; rfl
  | inr p =>
    rcases p with ⟨address, c⟩
    by_cases h : address = target
    · subst address
      simp [cellSubstitution, BitSubstitution.eval, certificateBitsOfInput]
    · simp [cellSubstitution, BitSubstitution.eval, certificateBitsOfInput, h]

def projectCell (tree : DecisionTree (CertificateCoordinates I T C) Output)
    (cores : I → T → Bool) (cells : (I → Bool) → C → Bool) (target : I → Bool) :
    DecisionTree C Output := tree.substitute (cellSubstitution cores cells target)

omit [DecidableEq I] in
@[simp] theorem projectCell_eval (tree : DecisionTree (CertificateCoordinates I T C) Output)
    (cores : I → T → Bool) (cells : (I → Bool) → C → Bool)
    (target : I → Bool) (word : C → Bool) :
    (projectCell tree cores cells target).eval word =
      tree.eval (certificateBitsOfInput ⟨cores, Function.update cells target word⟩) := by
  simp [projectCell]

omit [DecidableEq I] in
theorem projectCell_cost (tree : DecisionTree (CertificateCoordinates I T C) Output)
    (cores : I → T → Bool) (cells : (I → Bool) → C → Bool)
    (target : I → Bool) (word : C → Bool) :
    (projectCell tree cores cells target).queryCost word =
      ownerCount cellOwner tree target
        (certificateBitsOfInput ⟨cores, Function.update cells target word⟩) := by
  rw [projectCell, queryCost_substitute, cellSubstitution_eval]
  unfold ownerCount
  congr 1
  funext coord
  cases coord with
  | inl p => cases p; simp [cellSubstitution, cellOwner]
  | inr p =>
    rcases p with ⟨address, c⟩
    by_cases h : address = target <;> simp [cellSubstitution, cellOwner, h]

omit [DecidableEq I] in
@[simp] theorem projectCell_cost_self (tree : DecisionTree (CertificateCoordinates I T C) Output)
    (cores : I → T → Bool) (cells : (I → Bool) → C → Bool) (target : I → Bool) :
    (projectCell tree cores cells target).queryCost (cells target) =
      ownerCount cellOwner tree target (certificateBitsOfInput ⟨cores, cells⟩) := by
  rw [projectCell_cost]
  simp

def fixCellsSubstitution (cells : (I → Bool) → C → Bool) :
    BitSubstitution (I × T) (CertificateCoordinates I T C)
  | .inl p => .inr (p, id)
  | .inr (address, c) => .inl (cells address c)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem fixCellsSubstitution_eval (cells : (I → Bool) → C → Bool)
    (x : I × T → Bool) :
    (fixCellsSubstitution cells).eval x =
      certificateBitsOfInput ⟨(fun i t => x (i, t)), cells⟩ := by
  funext coord
  cases coord with
  | inl p => cases p; rfl
  | inr p => cases p; rfl

/-- Recording happens before cell bits are substituted by constants; the
returned list therefore retains the original cell-query counts. -/
noncomputable def coreListTree (threshold L : ℕ)
    (tree : DecisionTree (CertificateCoordinates I T C) Output)
    (cells : (I → Bool) → C → Bool) : DecisionTree (I × T) (Fin L → I → Bool) :=
  (heavyListTree cellOwner threshold L (fun _ => false) tree).substitute (fixCellsSubstitution cells)

theorem coreListTree_depth_le (threshold L : ℕ)
    (tree : DecisionTree (CertificateCoordinates I T C) Output)
    (cells : (I → Bool) → C → Bool) : (coreListTree threshold L tree cells).depth ≤ tree.depth := by
  unfold coreListTree
  exact (depth_substitute_le _ _).trans_eq (depth_heavyListTree _ _ _ _ _)

theorem coreListTree_contains_owner (threshold L Q : ℕ)
    (tree : DecisionTree (CertificateCoordinates I T C) Output)
    (hdepth : tree.depth ≤ Q) (hL : Q / (threshold + 1) ≤ L)
    (cores : I → T → Bool) (cells : (I → Bool) → C → Bool) (target : I → Bool)
    (hheavy : threshold < ownerCount cellOwner tree target (certificateBitsOfInput ⟨cores, cells⟩)) :
    ∃ j : Fin L, (coreListTree threshold L tree cells).eval (fun p => cores p.1 p.2) j = target := by
  have h := heavyListTree_contains cellOwner threshold L Q (fun _ => false) tree hdepth hL
    (certificateBitsOfInput ⟨cores, cells⟩) target hheavy
  simpa only [coreListTree, eval_substitute, fixCellsSubstitution_eval] using h

theorem coreListTree_contains (threshold L Q : ℕ)
    (tree : DecisionTree (CertificateCoordinates I T C) Output)
    (hdepth : tree.depth ≤ Q) (hL : Q / (threshold + 1) ≤ L)
    (cores : I → T → Bool) (cells : (I → Bool) → C → Bool) (target : I → Bool)
    (hheavy : threshold < (projectCell tree cores cells target).queryCost (cells target)) :
    ∃ j : Fin L, (coreListTree threshold L tree cells).eval (fun p => cores p.1 p.2) j = target := by
  apply coreListTree_contains_owner threshold L Q tree hdepth hL cores cells target
  simpa only [projectCell_cost_self] using hheavy

end QueryComplexity.CellProjection
