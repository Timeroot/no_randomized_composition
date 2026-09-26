import QueryComplexity.Algorithms
import QueryComplexity.Pointer
import QueryComplexity.PointerVerification
import QueryComplexity.PointerBias

/-! Binary decision trees implementing the pointer detector's query program. -/

namespace QueryComplexity.Pointer

universe u

variable {q : ℕ} {C : Type u} [Fintype C]

/-- Decode one cell after querying its entire bit encoding. -/
noncomputable def readCell (decode : (C → Bool) → PointerCell q) (ij : Fin q × Fin q) :
    DecisionTree ((Fin q × Fin q) × C) (PointerCell q) :=
  (DecisionTree.readCoordinates (fun c => (ij, c))).mapOutput decode

@[simp] theorem readCell_eval (decode : (C → Bool) → PointerCell q)
    (ij : Fin q × Fin q) (x : (Fin q × Fin q) × C → Bool) :
    (readCell decode ij).eval x = decodeInput decode x ij.1 ij.2 := by
  simp only [readCell, DecisionTree.eval_mapOutput, DecisionTree.eval_readCoordinates]
  rfl

theorem readCell_depth_le (decode : (C → Bool) → PointerCell q) (ij : Fin q × Fin q) :
    (readCell decode ij).depth ≤ Fintype.card C := by
  simpa only [readCell, DecisionTree.depth_mapOutput] using
    DecisionTree.depth_readCoordinates_le (fun c : C => (ij, c))

/-- Read and decode every cell of a column. -/
noncomputable def readColumn (decode : (C → Bool) → PointerCell q) (j : Fin q) :
    DecisionTree ((Fin q × Fin q) × C) (Fin q → PointerCell q) :=
  (DecisionTree.readCoordinates (fun rc : Fin q × C => ((rc.1, j), rc.2))).mapOutput
    (fun bits r => decode (fun c => bits (r, c)))

@[simp] theorem readColumn_eval (decode : (C → Bool) → PointerCell q) (j : Fin q)
    (x : (Fin q × Fin q) × C → Bool) :
    (readColumn decode j).eval x = fun r => decodeInput decode x r j := by
  simp only [readColumn, DecisionTree.eval_mapOutput, DecisionTree.eval_readCoordinates]
  rfl

theorem readColumn_depth_le (decode : (C → Bool) → PointerCell q) (j : Fin q) :
    (readColumn decode j).depth ≤ q * Fintype.card C := by
  simpa [readColumn] using
    DecisionTree.depth_readCoordinates_le (fun rc : Fin q × C => ((rc.1, j), rc.2))

/-- Read one specified cell from every column. -/
noncomputable def readLinked (decode : (C → Bool) → PointerCell q) (linked : Fin q → Fin q) :
    DecisionTree ((Fin q × Fin q) × C) (Fin q → PointerCell q) :=
  (DecisionTree.readCoordinates (fun cb : Fin q × C => ((linked cb.1, cb.1), cb.2))).mapOutput
    (fun bits c => decode (fun b => bits (c, b)))

@[simp] theorem readLinked_eval (decode : (C → Bool) → PointerCell q) (linked : Fin q → Fin q)
    (x : (Fin q × Fin q) × C → Bool) :
    (readLinked decode linked).eval x = fun c => decodeInput decode x (linked c) c := by
  simp only [readLinked, DecisionTree.eval_mapOutput, DecisionTree.eval_readCoordinates]
  rfl

theorem readLinked_depth_le (decode : (C → Bool) → PointerCell q) (linked : Fin q → Fin q) :
    (readLinked decode linked).depth ≤ q * Fintype.card C := by
  simpa [readLinked] using
    DecisionTree.depth_readCoordinates_le (fun cb : Fin q × C => ((linked cb.1, cb.1), cb.2))

/-- Fill irrelevant cells arbitrarily using the decoded queried data. -/
def verificationInput (j : Fin q) (column selected : Fin q → PointerCell q) : PointerInput q :=
  fun r c => if c = j then column r else selected c

/-- A full candidate verifier using its column and its canonically linked cells. -/
noncomputable def verifyTree (decode : (C → Bool) → PointerCell q) (i j : Fin q) :
    DecisionTree ((Fin q × Fin q) × C) Bool := by
  classical
  exact (readColumn decode j).bind fun column =>
    let linked := fun c => ((column i).row c).getD i
    (readLinked decode linked).mapOutput fun selected =>
      decide (Valid (verificationInput j column selected) i j linked)

theorem verifyTree_depth_le (decode : (C → Bool) → PointerCell q) (i j : Fin q) :
    (verifyTree decode i j).depth ≤ 2 * q * Fintype.card C := by
  have h : (verifyTree decode i j).depth ≤ q * Fintype.card C + q * Fintype.card C := by
    apply DecisionTree.depth_bind_le_add _ _ (readColumn_depth_le decode j)
    intro column
    simpa using readLinked_depth_le decode (fun c => ((column i).row c).getD i)
  nlinarith

theorem verifyTree_correct (decode : (C → Bool) → PointerCell q) (i j : Fin q)
    (x : (Fin q × Fin q) × C → Bool) :
    (verifyTree decode i j).eval x = true ↔ ∃ linked, Valid (decodeInput decode x) i j linked := by
  classical
  simp only [verifyTree, DecisionTree.eval_bind, readColumn_eval,
    DecisionTree.eval_mapOutput, readLinked_eval, decide_eq_true_eq]
  rw [exists_valid_iff_canonical]
  apply valid_iff_of_agree
  · intro r
    simp [verificationInput]
  · intro c hc
    simp [verificationInput, hc]

/-- Detector search modes. In a candidate or elimination mode, `nextRow` is
the first row of the sampled column that has not yet been scanned. -/
inductive SearchState (q : ℕ) where
  | scan (nextRow : ℕ) (survivors : Finset (Fin q))
  | candidate (nextRow : ℕ) (survivors : Finset (Fin q))
      (scannedRow candidateRow candidateColumn : Fin q)
  | eliminate (nextRow : ℕ) (survivors : Finset (Fin q))
      (candidateRow candidateColumn : Fin q) (candidateCell : PointerCell q)

abbrev SearchStep (q : ℕ) :=
  QueryStep (Fin q × Fin q) (PointerCell q) (SearchState q) (Option (Fin q × Fin q))

/-- Scan one row of the sampled column and, when possible, launch its candidate. -/
def scanStep (sampledColumn : Fin q) (nextRow : ℕ) (survivors : Finset (Fin q)) :
    SearchStep q :=
  if hrow : nextRow < q then
    .ask (⟨nextRow, hrow⟩, sampledColumn) fun cell =>
      if cell.bit then .scan (nextRow + 1) survivors
      else match cell.col with
      | none => .scan (nextRow + 1) survivors
      | some j =>
          if j ∈ survivors then
            match cell.row j with
            | none => .scan (nextRow + 1) survivors
            | some i => .candidate (nextRow + 1) survivors ⟨nextRow, hrow⟩ i j
          else .scan (nextRow + 1) survivors
  else .done none

/-- Candidate elimination retains the launched candidate column. A failed
launch resumes scanning; a successful query removes one other column. -/
def searchStep (sampledColumn : Fin q) : SearchState q → SearchStep q
  | .scan row survivors => scanStep sampledColumn row survivors
  | .candidate row survivors scanned i j =>
      .ask (i, j) fun cell =>
        if cell.row sampledColumn = some scanned then .eliminate row survivors i j cell
        else .scan row survivors
  | .eliminate row survivors i j cell =>
      if hnonempty : (survivors.erase j).Nonempty then
        let other := (survivors.erase j).min' hnonempty
        match cell.row other with
        | none => scanStep sampledColumn row survivors
        | some linkedRow => .ask (linkedRow, other) fun linkedCell =>
            if linkedCell.bit then .scan row survivors
            else .eliminate row (survivors.erase other) i j cell
      else .done (some (i, j))

/-- The potential accounts for the remaining scans, failed launches, and
successful eliminations. -/
def searchPotential : SearchState q → ℕ
  | .scan row survivors => 3 * (q - row) + survivors.card + 1
  | .candidate row survivors _ _ _ => 3 * (q - row) + survivors.card + 3
  | .eliminate row survivors _ _ _ => 3 * (q - row) + survivors.card + 2

/-- The columns on which the detector must accept a valid pointer input. -/
def GoodColumn (x : PointerInput q) (i j : Fin q) (linked : Fin q → Fin q) (sampled : Fin q) : Prop :=
  sampled ≠ j ∧ good x i j (linked sampled) sampled

def SearchInvariant (x : PointerInput q) (sampled i j : Fin q) (linked : Fin q → Fin q) :
    SearchState q → Prop
  | .scan row survivors => j ∈ survivors ∧
      (GoodColumn x i j linked sampled → row ≤ (linked sampled).val)
  | .candidate row survivors scanned ci cj =>
      j ∈ survivors ∧ cj ∈ survivors ∧
      (x scanned sampled).bit = false ∧ (x scanned sampled).col = some cj ∧
      (x scanned sampled).row cj = some ci ∧
      (GoodColumn x i j linked sampled →
        row ≤ (linked sampled).val ∨ (ci = i ∧ cj = j ∧ scanned = linked sampled))
  | .eliminate row survivors ci cj cell =>
      j ∈ survivors ∧ cj ∈ survivors ∧ cell = x ci cj ∧
      (cj = j → ci = i ∧ GoodColumn x i j linked sampled) ∧
      (GoodColumn x i j linked sampled → row ≤ (linked sampled).val ∨ (ci = i ∧ cj = j))

def SearchResult (x : PointerInput q) (sampled i j : Fin q) (linked : Fin q → Fin q)
    (answer : Option (Fin q × Fin q)) : Prop :=
  (GoodColumn x i j linked sampled → answer = some (i, j)) ∧
    (¬ GoodColumn x i j linked sampled → answer = none)

/-- A reciprocal launch into the special column must be the true special
cell, reached through the designated good linked cell. -/
theorem reciprocal_special {x : PointerInput q} {sampled i j ci scanned : Fin q}
    {linked : Fin q → Fin q} (hv : Valid x i j linked)
    (hzero : (x scanned sampled).bit = false)
    (hcol : (x scanned sampled).col = some j)
    (hrow : (x scanned sampled).row j = some ci)
    (hback : (x ci j).row sampled = some scanned) :
    ci = i ∧ GoodColumn x i j linked sampled := by
  have hsampled : sampled ≠ j := by
    intro heq
    subst sampled
    have hone := hv.1 scanned
    rw [hzero] at hone
    cases hone
  have hci : ci = i := by
    by_contra hne
    have hn := hv.2.1 ci hne sampled hsampled
    rw [hback] at hn
    cases hn
  subst ci
  have hptr := (hv.2.2.1 sampled hsampled).1
  have hscanned : scanned = linked sampled := Option.some.inj (hback.symm.trans hptr)
  refine ⟨rfl, hsampled, ?_⟩
  subst scanned
  exact ⟨hcol, hrow⟩

theorem scanStep_spec {x : PointerInput q} {sampled i j : Fin q} {linked : Fin q → Fin q}
    (hv : Valid x i j linked) (row : ℕ) (survivors : Finset (Fin q))
    (hinv : SearchInvariant x sampled i j linked (.scan row survivors)) :
    match scanStep sampled row survivors with
    | .done answer => SearchResult x sampled i j linked answer
    | .ask query next => SearchInvariant x sampled i j linked (next (x query.1 query.2)) ∧
        searchPotential (next (x query.1 query.2)) < searchPotential (.scan row survivors) := by
  classical
  by_cases hrow : row < q
  · let scanned : Fin q := ⟨row, hrow⟩
    let cell := x scanned sampled
    have hfull (hg : GoodColumn x i j linked sampled) (hr : row = (linked sampled).val) :
        cell.bit = false ∧ cell.col = some j ∧ cell.row j = some i := by
      have heq : scanned = linked sampled := Fin.ext hr
      dsimp [cell]
      rw [heq]
      exact ⟨(hv.2.2.1 sampled hg.1).2, hg.2.1, hg.2.2⟩
    have hscan (hbad : ¬ (cell.bit = false ∧ cell.col = some j ∧ cell.row j = some i)) :
        SearchInvariant x sampled i j linked (.scan (row + 1) survivors) ∧
        searchPotential (.scan (row + 1) survivors) < searchPotential (.scan row survivors) := by
      refine ⟨⟨hinv.1, ?_⟩, ?_⟩
      · intro hg
        have hle := hinv.2 hg
        have hne : row ≠ (linked sampled).val := fun hr => hbad (hfull hg hr)
        omega
      · simp only [searchPotential]
        omega
    have hcand (ci cj : Fin q) (hz : cell.bit = false) (hc : cell.col = some cj)
        (hm : cj ∈ survivors) (hp : cell.row cj = some ci) :
        SearchInvariant x sampled i j linked (.candidate (row + 1) survivors scanned ci cj) ∧
        searchPotential (.candidate (row + 1) survivors scanned ci cj) <
          searchPotential (.scan row survivors) := by
      refine ⟨⟨hinv.1, hm, hz, hc, hp, ?_⟩, ?_⟩
      · intro hg
        have hle := hinv.2 hg
        by_cases hr : row = (linked sampled).val
        · obtain ⟨_, hfc, hfp⟩ := hfull hg hr
          have hcj : cj = j := Option.some.inj (hc.symm.trans hfc)
          have hci : ci = i := by
            subst cj
            exact Option.some.inj (hp.symm.trans hfp)
          exact Or.inr ⟨hci, hcj, Fin.ext hr⟩
        · exact Or.inl (by omega)
      · simp only [searchPotential]
        omega
    simp only [scanStep, dif_pos hrow]
    change (SearchInvariant x sampled i j linked _ ∧ searchPotential _ < _) 
    cases hb : cell.bit with
    | true => simpa only [hb, ↓reduceIte] using hscan (by simp [hb])
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases hc : cell.col with
        | none => simpa only [hc] using hscan (by simp [hc])
        | some cj =>
            by_cases hm : cj ∈ survivors
            · simp only [hm, ↓reduceIte]
              cases hp : cell.row cj with
              | none =>
                  apply hscan
                  intro h
                  have heq : cj = j := Option.some.inj (hc.symm.trans h.2.1)
                  subst cj
                  rw [hp] at h
                  cases h.2.2
              | some ci => exact hcand ci cj hb hc hm hp
            · simp only [hm, ↓reduceIte]
              apply hscan
              intro h
              have heq : cj = j := Option.some.inj (hc.symm.trans h.2.1)
              subst cj
              exact hm hinv.1
  · simp only [scanStep, dif_neg hrow]
    refine ⟨?_, fun _ => rfl⟩
    intro hg
    have hle := hinv.2 hg
    have hlt := (linked sampled).isLt
    omega

theorem searchStep_spec {x : PointerInput q} {sampled i j : Fin q} {linked : Fin q → Fin q}
    (hv : Valid x i j linked) (state : SearchState q)
    (hinv : SearchInvariant x sampled i j linked state) :
    match searchStep sampled state with
    | .done answer => SearchResult x sampled i j linked answer
    | .ask query next => SearchInvariant x sampled i j linked (next (x query.1 query.2)) ∧
        searchPotential (next (x query.1 query.2)) < searchPotential state := by
  classical
  cases state with
  | scan row survivors => exact scanStep_spec hv row survivors hinv
  | candidate row survivors scanned ci cj =>
      rcases hinv with ⟨hj, hcj, hz, hc, hp, hprogress⟩
      simp only [searchStep]
      by_cases hback : (x ci cj).row sampled = some scanned
      · simp only [hback, ↓reduceIte]
        refine ⟨⟨hj, hcj, rfl, ?_, ?_⟩, ?_⟩
        · intro heq
          subst cj
          exact reciprocal_special hv hz hc hp hback
        · intro hg
          rcases hprogress hg with hle | ⟨hci, hcj, _⟩
          · exact Or.inl hle
          · exact Or.inr ⟨hci, hcj⟩
        · simp only [searchPotential]
          omega
      · simp only [hback, ↓reduceIte]
        refine ⟨⟨hj, ?_⟩, ?_⟩
        · intro hg
          rcases hprogress hg with hle | ⟨hci, hcj, hscanned⟩
          · exact hle
          · subst ci
            subst cj
            subst scanned
            exact (hback (hv.2.2.1 sampled hg.1).1).elim
        · simp only [searchPotential]
          omega
  | eliminate row survivors ci cj cell =>
      rcases hinv with ⟨hj, hcj, hcell, hsafe, hprogress⟩
      subst cell
      by_cases hnonempty : (survivors.erase cj).Nonempty
      · let other := (survivors.erase cj).min' hnonempty
        have hmem : other ∈ survivors.erase cj := Finset.min'_mem _ _
        have hother : other ≠ cj := (Finset.mem_erase.mp hmem).1
        have hsurvivor : other ∈ survivors := (Finset.mem_erase.mp hmem).2
        simp only [searchStep, dif_pos hnonempty]
        change match (match (x ci cj).row other with
          | none => scanStep sampled row survivors
          | some linkedRow => QueryStep.ask (linkedRow, other) (fun linkedCell =>
              if linkedCell.bit then SearchState.scan row survivors
              else SearchState.eliminate row (survivors.erase other) ci cj (x ci cj))) with
          | .done answer => SearchResult x sampled i j linked answer
          | .ask query next => SearchInvariant x sampled i j linked (next (x query.1 query.2)) ∧
              searchPotential (next (x query.1 query.2)) <
                searchPotential (.eliminate row survivors ci cj (x ci cj))
        cases hp : (x ci cj).row other with
        | none =>
            have hscan : SearchInvariant x sampled i j linked (.scan row survivors) := by
              refine ⟨hj, ?_⟩
              intro hg
              rcases hprogress hg with hle | ⟨hci, hcj⟩
              · exact hle
              · subst ci
                subst cj
                have hptr := (hv.2.2.1 other hother).1
                rw [hp] at hptr
                cases hptr
            have hs := scanStep_spec hv row survivors hscan
            cases hstep : scanStep sampled row survivors with
            | done answer => simpa only [hp, hstep] using hs
            | ask query next =>
                simp only [hstep] at hs
                refine ⟨hs.1, hs.2.trans ?_⟩
                simp only [searchPotential]
                omega
        | some linkedRow =>
            dsimp only
            cases hb : (x linkedRow other).bit with
            | true =>
                simp only [↓reduceIte]
                refine ⟨⟨hj, ?_⟩, ?_⟩
                · intro hg
                  rcases hprogress hg with hle | ⟨hci, hcj⟩
                  · exact hle
                  · subst ci
                    subst cj
                    have hptr := (hv.2.2.1 other hother).1
                    have hlinked : linkedRow = linked other := Option.some.inj (hp.symm.trans hptr)
                    have hz := (hv.2.2.1 other hother).2
                    rw [← hlinked, hb] at hz
                    cases hz
                · simp only [searchPotential]
                  omega
            | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                have hotherj : other ≠ j := by
                  intro heq
                  have hone := hv.1 linkedRow
                  rw [← heq, hb] at hone
                  cases hone
                refine ⟨⟨Finset.mem_erase.mpr ⟨Ne.symm hotherj, hj⟩,
                  Finset.mem_erase.mpr ⟨Ne.symm hother, hcj⟩, rfl, hsafe, hprogress⟩, ?_⟩
                have hcard := Finset.card_erase_of_mem hsurvivor
                have hpos : 0 < survivors.card := Finset.card_pos.mpr ⟨other, hsurvivor⟩
                simp only [searchPotential]
                omega
      · simp only [searchStep, dif_neg hnonempty]
        have heq : cj = j := by
          by_contra hne
          exact hnonempty ⟨j, Finset.mem_erase.mpr ⟨Ne.symm hne, hj⟩⟩
        obtain ⟨hci, hg⟩ := hsafe heq
        subst ci
        subst cj
        exact ⟨fun _ => rfl, fun hn => (hn hg).elim⟩

@[simp] theorem searchPotential_initial :
    searchPotential (.scan 0 (Finset.univ : Finset (Fin q))) = 4 * q + 1 := by
  simp [searchPotential]
  omega

/-- On every valid input the capped search returns the special cell exactly
for good sampled columns. The potential proves the cap is sufficient. -/
theorem searchRun_result {x : PointerInput q} {sampled i j : Fin q} {linked : Fin q → Fin q}
    (hv : Valid x i j linked) :
    SearchResult x sampled i j linked
      (QueryStep.run (searchStep sampled) none (fun ij => x ij.1 ij.2) (4 * q + 2)
        (.scan 0 Finset.univ)) := by
  apply QueryStep.run_spec_of_decreasing (searchStep sampled) none
    (fun ij => x ij.1 ij.2) (SearchInvariant x sampled i j linked)
    (SearchResult x sampled i j linked) searchPotential
    (fun state hstate => by
      have hs := searchStep_spec hv state hstate
      cases heq : searchStep sampled state <;> simpa only [heq] using hs)
  · exact ⟨Finset.mem_univ _, fun _ => Nat.zero_le _⟩
  · rw [searchPotential_initial]
    omega

/-- The search is represented by a genuine binary tree, with an explicit cap. -/
noncomputable def searchTree (decode : (C → Bool) → PointerCell q) (sampledColumn : Fin q) :
    DecisionTree ((Fin q × Fin q) × C) (Option (Fin q × Fin q)) :=
  QueryStep.compile (searchStep sampledColumn) none (readCell decode) (4 * q + 2)
    (.scan 0 Finset.univ)

theorem searchTree_depth_le (decode : (C → Bool) → PointerCell q) (sampledColumn : Fin q) :
    (searchTree decode sampledColumn).depth ≤ (4 * q + 2) * Fintype.card C :=
  QueryStep.depth_compile_le _ _ _ (readCell_depth_le decode) _ _

theorem searchTree_eval (decode : (C → Bool) → PointerCell q) (sampledColumn : Fin q)
    (x : (Fin q × Fin q) × C → Bool) :
    (searchTree decode sampledColumn).eval x =
      QueryStep.run (searchStep sampledColumn) none
        (fun ij => decodeInput decode x ij.1 ij.2) (4 * q + 2) (.scan 0 Finset.univ) :=
  QueryStep.eval_compile _ _ _ _ (readCell_eval decode) _ _ _

theorem searchTree_result (decode : (C → Bool) → PointerCell q)
    (x : (Fin q × Fin q) × C → Bool) {sampled i j : Fin q} {linked : Fin q → Fin q}
    (hv : Valid (decodeInput decode x) i j linked) :
    SearchResult (decodeInput decode x) sampled i j linked ((searchTree decode sampled).eval x) := by
  rw [searchTree_eval]
  exact searchRun_result hv

/-- Search and then run a full verifier on the selected candidate, if one exists. -/
noncomputable def detectorTree (decode : (C → Bool) → PointerCell q)
    (verify : Fin q → Fin q → DecisionTree ((Fin q × Fin q) × C) Bool)
    (sampledColumn : Fin q) : DecisionTree ((Fin q × Fin q) × C) Bool :=
  (searchTree decode sampledColumn).bind fun candidate =>
    match candidate with
    | none => .leaf false
    | some (i, j) => verify i j

theorem detectorTree_depth_le (decode : (C → Bool) → PointerCell q)
    (verify : Fin q → Fin q → DecisionTree ((Fin q × Fin q) × C) Bool)
    {cost : ℕ} (hverify : ∀ i j, (verify i j).depth ≤ cost) (sampledColumn : Fin q) :
    (detectorTree decode verify sampledColumn).depth ≤ (4 * q + 2) * Fintype.card C + cost := by
  apply DecisionTree.depth_bind_le_add _ _ (searchTree_depth_le decode sampledColumn)
  intro candidate
  cases candidate with
  | none => exact Nat.zero_le _
  | some ij => exact hverify ij.1 ij.2

/-- The complete detector, including the actual candidate verifier. -/
noncomputable def fullDetectorTree (decode : (C → Bool) → PointerCell q) (sampledColumn : Fin q) :
    DecisionTree ((Fin q × Fin q) × C) Bool :=
  detectorTree decode (verifyTree decode) sampledColumn

theorem fullDetectorTree_depth_le (decode : (C → Bool) → PointerCell q) (sampledColumn : Fin q) :
    (fullDetectorTree decode sampledColumn).depth ≤ (6 * q + 2) * Fintype.card C := by
  have h := detectorTree_depth_le decode (verifyTree decode) (verifyTree_depth_le decode) sampledColumn
  change (fullDetectorTree decode sampledColumn).depth ≤ _ at h
  nlinarith

/-- Acceptance implies the full pointer predicate, on every input. -/
theorem fullDetectorTree_sound (decode : (C → Bool) → PointerCell q) (sampledColumn : Fin q)
    (x : (Fin q × Fin q) × C → Bool) (h : (fullDetectorTree decode sampledColumn).eval x = true) :
    encoded decode x = true := by
  simp only [fullDetectorTree, detectorTree, DecisionTree.eval_bind] at h
  cases hs : (searchTree decode sampledColumn).eval x with
  | none => simp [hs, DecisionTree.eval] at h
  | some ij =>
      simp only [hs] at h
      obtain ⟨linked, hv⟩ := (verifyTree_correct decode ij.1 ij.2 x).1 h
      exact (value_eq_true_iff _).2 ⟨ij.1, ij.2, linked, hv⟩

theorem fullDetectorTree_true_iff (decode : (C → Bool) → PointerCell q)
    (x : (Fin q × Fin q) × C → Bool) {sampled i j : Fin q} {linked : Fin q → Fin q}
    (hv : Valid (decodeInput decode x) i j linked) :
    (fullDetectorTree decode sampled).eval x = true ↔
      GoodColumn (decodeInput decode x) i j linked sampled := by
  classical
  have hs := searchTree_result decode x (sampled := sampled) hv
  by_cases hg : GoodColumn (decodeInput decode x) i j linked sampled
  · have hsearch := hs.1 hg
    have hverify := (verifyTree_correct decode i j x).2 ⟨linked, hv⟩
    simp [fullDetectorTree, detectorTree, hsearch, hverify, hg]
  · have hsearch := hs.2 hg
    simp [fullDetectorTree, detectorTree, hsearch, DecisionTree.eval, hg]

/-- Uniformly sample the scanned column. -/
noncomputable def detector (decode : (C → Bool) → PointerCell q) (hq : 0 < q) :
    FiniteRandomizedTree (Fin q) ((Fin q × Fin q) × C) Bool := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  exact FiniteRandomizedTree.uniform (fullDetectorTree decode)

theorem detector_depthBound (decode : (C → Bool) → PointerCell q) (hq : 0 < q) :
    (detector decode hq).DepthBound ((6 * q + 2) * Fintype.card C) :=
  fullDetectorTree_depth_le decode

theorem detector_rejects_zero (decode : (C → Bool) → PointerCell q) (hq : 0 < q)
    (x : (Fin q × Fin q) × C → Bool) (hzero : encoded decode x = false) :
    (detector decode hq).probability (fun b => b = true) x = 0 := by
  classical
  unfold FiniteRandomizedTree.probability
  apply Finset.sum_eq_zero
  intro j _
  have hn : (fullDetectorTree decode j).eval x ≠ true := by
    intro h
    have := fullDetectorTree_sound decode j x h
    rw [hzero] at this
    cases this
  simp [detector, FiniteRandomizedTree.uniform, hn]

/-- Every positive input has the same exact acceptance probability. -/
theorem detector_probability_on_valid (decode : (C → Bool) → PointerCell q) (hq : 0 < q)
    (x : (Fin q × Fin q) × C → Bool) {i j : Fin q} {linked : Fin q → Fin q}
    (hv : Valid (decodeInput decode x) i j linked) :
    (detector decode hq).probability (fun b => b = true) x =
      (((q - 1) / 2 : ℕ) : ℝ) / (q : ℝ) := by
  classical
  have hcard : (Finset.univ.filter
      (fun sampled => GoodColumn (decodeInput decode x) i j linked sampled)).card = (q - 1) / 2 := by
    convert hv.2.2.2 using 1
    congr 1
    ext sampled
    simp [GoodColumn]
  calc
    _ = ∑ sampled : Fin q,
        if GoodColumn (decodeInput decode x) i j linked sampled then (q : ℝ)⁻¹ else 0 := by
      unfold FiniteRandomizedTree.probability
      apply Finset.sum_congr rfl
      intro sampled _
      by_cases hg : GoodColumn (decodeInput decode x) i j linked sampled
      · have ht := (fullDetectorTree_true_iff decode x hv).2 hg
        simp [detector, FiniteRandomizedTree.uniform, ht, hg]
      · have ht : (fullDetectorTree decode sampled).eval x ≠ true :=
          fun ht => hg ((fullDetectorTree_true_iff decode x hv).1 ht)
        simp [detector, FiniteRandomizedTree.uniform, ht, hg]
    _ = ((Finset.univ.filter
        (fun sampled => GoodColumn (decodeInput decode x) i j linked sampled)).card : ℝ) *
          (q : ℝ)⁻¹ := by
      rw [← Finset.sum_filter]
      simp
    _ = _ := by rw [hcard, div_eq_mul_inv]

/-- The detector's exact acceptance law on all total inputs. -/
theorem detector_probability (decode : (C → Bool) → PointerCell q) (hq : 0 < q)
    (x : (Fin q × Fin q) × C → Bool) :
    (detector decode hq).probability (fun b => b = true) x =
      if encoded decode x then (((q - 1) / 2 : ℕ) : ℝ) / (q : ℝ) else 0 := by
  cases hx : encoded decode x with
  | false => simpa only [hx, Bool.false_eq_true, ↓reduceIte] using detector_rejects_zero decode hq x hx
  | true =>
      obtain ⟨i, j, linked, hv⟩ := (value_eq_true_iff (decodeInput decode x)).1 hx
      simpa only [hx, ↓reduceIte] using detector_probability_on_valid decode hq x hv

/-- Run the pointer detector on one block of the majority composition. -/
noncomputable def blockDetector (decode : (C → Bool) → PointerCell q) (hq : 0 < q) (block : Fin q) :
    FiniteRandomizedTree (Fin q) (Fin q × ((Fin q × Fin q) × C)) Bool :=
  (detector decode hq).substitute (fun coordinate => .inr ((block, coordinate), id))

theorem blockDetector_probability (decode : (C → Bool) → PointerCell q) (hq : 0 < q)
    (block : Fin q) (x : Fin q × ((Fin q × Fin q) × C) → Bool) :
    (blockDetector decode hq block).probability (fun b => b = true) x =
      if encoded decode (fun coordinate => x (block, coordinate))
        then (((q - 1) / 2 : ℕ) : ℝ) / (q : ℝ) else 0 := by
  unfold blockDetector
  rw [FiniteRandomizedTree.probability_substitute]
  exact detector_probability decode hq _

/-- Select the majority block uniformly, and then run its pointer detector. -/
noncomputable def sampledBlockDetector (decode : (C → Bool) → PointerCell q) (hq : 0 < q) :
    FiniteRandomizedTree (Fin q × Fin q) (Fin q × ((Fin q × Fin q) × C)) Bool := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  exact FiniteRandomizedTree.uniformChoice (blockDetector decode hq)

theorem sampledBlockDetector_depthBound (decode : (C → Bool) → PointerCell q) (hq : 0 < q) :
    (sampledBlockDetector decode hq).DepthBound ((6 * q + 2) * Fintype.card C) := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  apply FiniteRandomizedTree.depthBound_uniformChoice
  intro block
  exact (detector decode hq).depthBound_substitute _ (detector_depthBound decode hq)

noncomputable def positiveCount (decode : (C → Bool) → PointerCell q)
    (x : Fin q × ((Fin q × Fin q) × C) → Bool) : ℕ :=
  (Finset.univ.filter (fun block => encoded decode (fun coordinate => x (block, coordinate)) = true)).card

theorem sampledBlockDetector_probability (decode : (C → Bool) → PointerCell q) (hq : 0 < q)
    (x : Fin q × ((Fin q × Fin q) × C) → Bool) :
    (sampledBlockDetector decode hq).probability (fun b => b = true) x =
      ((((q - 1) / 2 : ℕ) : ℝ) / (q : ℝ)) * (positiveCount decode x : ℝ) / (q : ℝ) := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  unfold sampledBlockDetector
  rw [FiniteRandomizedTree.probability_uniformChoice]
  simp only [Fintype.card_fin]
  have hsum : (∑ block : Fin q, (blockDetector decode hq block).probability (fun b => b = true) x) =
      (positiveCount decode x : ℝ) * ((((q - 1) / 2 : ℕ) : ℝ) / (q : ℝ)) := by
    simp_rw [blockDetector_probability]
    rw [← Finset.sum_filter]
    simp [positiveCount]
  rw [hsum]
  ring

/-- Balance the sampled detector with an independent biased coin. The choice
of `alpha` is explicit; the bias theorem selects `(1-rho)/(2-rho)`. -/
noncomputable def weakEvaluator (decode : (C → Bool) → PointerCell q) (hq : 0 < q)
    (alpha : ℝ) (ha₀ : 0 ≤ alpha) (ha₁ : alpha ≤ 1) :
    FiniteRandomizedTree (Bool × (Fin q × Fin q)) (Fin q × ((Fin q × Fin q) × C)) Bool :=
  (FiniteRandomizedTree.coin alpha ha₀ ha₁).or (sampledBlockDetector decode hq)

theorem weakEvaluator_depthBound (decode : (C → Bool) → PointerCell q) (hq : 0 < q)
    (alpha : ℝ) (ha₀ : 0 ≤ alpha) (ha₁ : alpha ≤ 1) :
    (weakEvaluator decode hq alpha ha₀ ha₁).DepthBound ((6 * q + 2) * Fintype.card C) := by
  have h := (FiniteRandomizedTree.coin alpha ha₀ ha₁).depthBound_or
    (sampledBlockDetector decode hq) (FiniteRandomizedTree.depthBound_coin alpha ha₀ ha₁)
    (sampledBlockDetector_depthBound decode hq)
  simpa only [Nat.zero_add] using h

theorem weakEvaluator_probability (decode : (C → Bool) → PointerCell q) (hq : 0 < q)
    (alpha : ℝ) (ha₀ : 0 ≤ alpha) (ha₁ : alpha ≤ 1)
    (x : Fin q × ((Fin q × Fin q) × C) → Bool) :
    (weakEvaluator decode hq alpha ha₀ ha₁).probability (fun b => b = true) x =
      alpha + (1 - alpha) *
        (((((q - 1) / 2 : ℕ) : ℝ) / (q : ℝ)) * (positiveCount decode x : ℝ) / (q : ℝ)) := by
  unfold weakEvaluator
  rw [FiniteRandomizedTree.probability_or_true, FiniteRandomizedTree.probability_coin_true,
    sampledBlockDetector_probability]

noncomputable def balancingAlpha (q : ℕ) : ℝ :=
  (1 - ((q : ℝ) - 1) / (2 * q)) / (2 - ((q : ℝ) - 1) / (2 * q))

theorem balancingAlpha_bounds (q : ℕ) (hq : 3 ≤ q) :
    0 ≤ balancingAlpha q ∧ balancingAlpha q ≤ 1 := by
  have hqr : (3 : ℝ) ≤ q := by exact_mod_cast hq
  obtain ⟨hlo, hhi⟩ := detector_rho_bounds (q : ℝ) hqr
  have hd : 0 < 2 - ((q : ℝ) - 1) / (2 * q) := by linarith
  constructor
  · exact div_nonneg (by linarith) hd.le
  · apply (div_le_one₀ hd).2
    linarith

/-- The specified weak randomized evaluator for the total inner function. -/
noncomputable def balancedWeakEvaluator (decode : (C → Bool) → PointerCell q) (hq : 3 ≤ q) :
    FiniteRandomizedTree (Bool × (Fin q × Fin q)) (Fin q × ((Fin q × Fin q) × C)) Bool :=
  weakEvaluator decode (by omega) (balancingAlpha q)
    (balancingAlpha_bounds q hq).1 (balancingAlpha_bounds q hq).2

theorem balancedWeakEvaluator_depthBound (decode : (C → Bool) → PointerCell q) (hq : 3 ≤ q) :
    (balancedWeakEvaluator decode hq).DepthBound ((6 * q + 2) * Fintype.card C) :=
  weakEvaluator_depthBound _ _ _ _ _

omit [Fintype C] in
theorem inner_eq_decide_count (decode : (C → Bool) → PointerCell q)
    (x : Fin q × ((Fin q × Fin q) × C) → Bool) :
    inner decode x = decide (q < 2 * positiveCount decode x) := rfl

/-- Uniform success bias for every input of the total inner function. -/
theorem balancedWeakEvaluator_success (decode : (C → Bool) → PointerCell q)
    (hq : 3 ≤ q) (hodd : Odd q) (x : Fin q × ((Fin q × Fin q) × C) → Bool) :
    (1 : ℝ) / 2 + 1 / (10 * q) ≤
      (balancedWeakEvaluator decode hq).probability (fun b => b = inner decode x) x := by
  have hp := weakEvaluator_probability decode (by omega : 0 < q) (balancingAlpha q)
    (balancingAlpha_bounds q hq).1 (balancingAlpha_bounds q hq).2 x
  change (balancedWeakEvaluator decode hq).probability (fun b => b = true) x = _ at hp
  rw [rho_discrete_eq q hodd] at hp
  have hsuccess := balanced_success q (positiveCount decode x) hq hodd
  dsimp only at hsuccess
  by_cases hmajor : q < 2 * positiveCount decode x
  · have hinner : inner decode x = true := by rw [inner_eq_decide_count]; simp [hmajor]
    rw [hinner, hp]
    simpa only [hmajor, if_true, balancingAlpha] using hsuccess
  · have hinner : inner decode x = false := by rw [inner_eq_decide_count]; simp [hmajor]
    rw [hinner, FiniteRandomizedTree.probability_false, hp]
    simpa only [hmajor, if_false, balancingAlpha] using hsuccess

end QueryComplexity.Pointer
