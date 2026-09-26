import QueryComplexity.Definitions
import Mathlib.Tactic

/-!
# Total certificate functions

These definitions isolate the totalization step used by the counterexample.
Certificates for distinct Boolean values must be incompatible.  A physical
cell may decode to any flag and tuple of witnesses: no promise on the cell
contents is imposed.  Consequently the resulting cheat-sheet function is a
total Boolean function, and a passing cell has a unique address.

This file proves logical correctness of the construction. It does not assume
or assert a query-complexity upper or lower bound for the verifier or decoder.
-/

namespace QueryComplexity

universe u v w z

/-- A certificate relation whose certificates cannot assert different values
on the same core input. Completeness is expressed by `DefinedAt` below. -/
structure CertificateSystem (Core : Type u) (Witness : Type v) where
  valid : Core → Bool → Witness → Prop
  compatible : ∀ {x b b' w w'}, valid x b w → valid x b' w' → b = b'

namespace CertificateSystem

variable {Core : Type u} {Witness : Type v}

/-- The partial core is defined with value `b` exactly when a certificate
for that value exists. -/
def DefinedAt (S : CertificateSystem Core Witness) (x : Core) (b : Bool) : Prop :=
  ∃ w, S.valid x b w

def InDomain (S : CertificateSystem Core Witness) (x : Core) : Prop :=
  ∃ b, S.DefinedAt x b

def Undefined (S : CertificateSystem Core Witness) (x : Core) : Prop :=
  ¬ S.InDomain x

theorem definedAt_unique (S : CertificateSystem Core Witness) {x : Core}
    {b b' : Bool} (h : S.DefinedAt x b) (h' : S.DefinedAt x b') : b = b' := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨w', hw'⟩ := h'
  exact S.compatible hw hw'

/-- An actual partial Boolean function, represented by `Option Bool`.
The two certified branches are disjoint by compatibility. -/
noncomputable def value (S : CertificateSystem Core Witness) (x : Core) : Option Bool := by
  classical
  exact if S.DefinedAt x true then some true
    else if S.DefinedAt x false then some false else none

theorem value_eq_some_iff (S : CertificateSystem Core Witness) (x : Core) (b : Bool) :
    S.value x = some b ↔ S.DefinedAt x b := by
  classical
  cases b with
  | false =>
      by_cases ht : S.DefinedAt x true
      · have hf : ¬ S.DefinedAt x false := by
          intro h
          have := S.definedAt_unique ht h
          cases this
        simp [value, ht, hf]
      · simp [value, ht]
  | true =>
      by_cases ht : S.DefinedAt x true
      · simp [value, ht]
      · simp [value, ht]

theorem value_eq_none_iff (S : CertificateSystem Core Witness) (x : Core) :
    S.value x = none ↔ S.Undefined x := by
  classical
  simp only [Undefined, InDomain, not_exists]
  constructor
  · intro h b hb
    have hs := (S.value_eq_some_iff x b).2 hb
    rw [h] at hs
    cases hs
  · intro h
    simp [value, h true, h false]

end CertificateSystem

/-- A tuple of core inputs and one physical cell for every Boolean address. -/
structure CertificateInput (I : Type w) (Core : Type u) (Cell : Type z) where
  cores : I → Core
  cells : (I → Bool) → Cell

/-- A decoder is an arbitrary total map. Its first output is the validity
flag and its second output supplies one certificate for each core. -/
abbrev CertificateDecoder (I : Type w) (Witness : Type v) (Cell : Type z) :=
  Cell → Bool × (I → Witness)

namespace CertificateInput

variable {I : Type w} {Core : Type u} {Witness : Type v} {Cell : Type z}

def AcceptsAt (S : CertificateSystem Core Witness)
    (decode : CertificateDecoder I Witness Cell)
    (x : CertificateInput I Core Cell) (address : I → Bool) : Prop :=
  (decode (x.cells address)).1 = true ∧
    ∀ i, S.valid (x.cores i) (address i) ((decode (x.cells address)).2 i)

/-- This is total even when a core is undefined, a cell has a zero flag,
or its witnesses are malformed. -/
noncomputable def cheatSheet (S : CertificateSystem Core Witness)
    (decode : CertificateDecoder I Witness Cell)
    (x : CertificateInput I Core Cell) : Bool := by
  classical
  exact decide (∃ address, x.AcceptsAt S decode address)

@[simp] theorem cheatSheet_eq_true_iff (S : CertificateSystem Core Witness)
    (decode : CertificateDecoder I Witness Cell) (x : CertificateInput I Core Cell) :
    x.cheatSheet S decode = true ↔ ∃ address, x.AcceptsAt S decode address := by
  classical
  simp [cheatSheet]

@[simp] theorem cheatSheet_eq_false_iff (S : CertificateSystem Core Witness)
    (decode : CertificateDecoder I Witness Cell) (x : CertificateInput I Core Cell) :
    x.cheatSheet S decode = false ↔ ¬ ∃ address, x.AcceptsAt S decode address := by
  classical
  simp [cheatSheet]

theorem acceptingAddress_unique (S : CertificateSystem Core Witness)
    (decode : CertificateDecoder I Witness Cell) (x : CertificateInput I Core Cell)
    {a b : I → Bool} (ha : x.AcceptsAt S decode a) (hb : x.AcceptsAt S decode b) : a = b := by
  funext i
  exact S.compatible (ha.2 i) (hb.2 i)

theorem acceptsAt_definedAt (S : CertificateSystem Core Witness)
    (decode : CertificateDecoder I Witness Cell) (x : CertificateInput I Core Cell)
    {a : I → Bool} (ha : x.AcceptsAt S decode a) (i : I) :
    S.DefinedAt (x.cores i) (a i) :=
  ⟨(decode (x.cells a)).2 i, ha.2 i⟩

theorem acceptingAddress_eq (S : CertificateSystem Core Witness)
    (decode : CertificateDecoder I Witness Cell) (x : CertificateInput I Core Cell)
    {a y : I → Bool} (ha : x.AcceptsAt S decode a)
    (hy : ∀ i, S.DefinedAt (x.cores i) (y i)) : a = y := by
  funext i
  exact S.definedAt_unique (x.acceptsAt_definedAt S decode ha i) (hy i)

/-- On defined cores, testing the unique correct address is equivalent to
evaluating the total predicate. -/
theorem cheatSheet_true_iff_correctCell (S : CertificateSystem Core Witness)
    (decode : CertificateDecoder I Witness Cell) (x : CertificateInput I Core Cell)
    (y : I → Bool) (hy : ∀ i, S.DefinedAt (x.cores i) (y i)) :
    x.cheatSheet S decode = true ↔ x.AcceptsAt S decode y := by
  rw [cheatSheet_eq_true_iff]
  constructor
  · rintro ⟨a, ha⟩
    have hay := x.acceptingAddress_eq S decode ha hy
    exact hay ▸ ha
  · exact fun h => ⟨y, h⟩

theorem undefinedCore_rejects (S : CertificateSystem Core Witness)
    (decode : CertificateDecoder I Witness Cell) (x : CertificateInput I Core Cell)
    (i : I) (hi : S.Undefined (x.cores i)) : x.cheatSheet S decode = false := by
  rw [cheatSheet_eq_false_iff]
  rintro ⟨a, ha⟩
  exact hi ⟨a i, x.acceptsAt_definedAt S decode ha i⟩

theorem zeroFlags_reject (S : CertificateSystem Core Witness)
    (decode : CertificateDecoder I Witness Cell) (x : CertificateInput I Core Cell)
    (hz : ∀ a, (decode (x.cells a)).1 = false) : x.cheatSheet S decode = false := by
  rw [cheatSheet_eq_false_iff]
  rintro ⟨a, ha⟩
  have h := ha.1
  rw [hz a] at h
  cases h

/-- Replace a single physical cell; this imposes no condition on other cells. -/
noncomputable def plantCell (x : CertificateInput I Core Cell)
    (a : I → Bool) (cell : Cell) : CertificateInput I Core Cell := by
  classical
  exact ⟨x.cores, Function.update x.cells a cell⟩

/-- Planting one valid flagged cell gives a positive input. Other cells
remain completely arbitrary. -/
theorem plantedCell_accepts (S : CertificateSystem Core Witness)
    (decode : CertificateDecoder I Witness Cell) (x : CertificateInput I Core Cell)
    (a : I → Bool) (witness : I → Witness) (cell : Cell)
    (hc : decode cell = (true, witness))
    (hw : ∀ i, S.valid (x.cores i) (a i) (witness i)) :
    (x.plantCell a cell).cheatSheet S decode = true := by
  classical
  rw [cheatSheet_eq_true_iff]
  refine ⟨a, ?_⟩
  simpa [AcceptsAt, plantCell, hc] using hw

end CertificateInput

/-- The actual Boolean coordinates: core coordinates and physical cell
coordinates occupy disjoint summands. -/
abbrev CertificateCoordinates (I : Type w) (T : Type u) (C : Type z) :=
  (I × T) ⊕ ((I → Bool) × C)

def certificateInputOfBits {I : Type w} {T : Type u} {C : Type z}
    (bits : CertificateCoordinates I T C → Bool) :
    CertificateInput I (T → Bool) (C → Bool) where
  cores i t := bits (.inl (i, t))
  cells address c := bits (.inr (address, c))

/-- Repacking a structured input imposes no promise on its bits. -/
def certificateBitsOfInput {I : Type w} {T : Type u} {C : Type z}
    (x : CertificateInput I (T → Bool) (C → Bool)) :
    CertificateCoordinates I T C → Bool
  | .inl (i, t) => x.cores i t
  | .inr (a, c) => x.cells a c

@[simp] theorem certificateInputOfBits_bitsOfInput
    {I : Type w} {T : Type u} {C : Type z}
    (x : CertificateInput I (T → Bool) (C → Bool)) :
    certificateInputOfBits (certificateBitsOfInput x) = x := by
  cases x
  rfl

@[simp] theorem certificateBitsOfInput_inputOfBits
    {I : Type w} {T : Type u} {C : Type z}
    (bits : CertificateCoordinates I T C → Bool) :
    certificateBitsOfInput (certificateInputOfBits bits) = bits := by
  funext coordinate
  cases coordinate with
  | inl p => cases p; rfl
  | inr p => cases p; rfl

/-- A total Boolean function in exactly the query model of `Definitions`. -/
noncomputable def certificateBoolFn {I : Type w} {T : Type u} {C : Type z}
    {Witness : Type v} (S : CertificateSystem (T → Bool) Witness)
    (decode : CertificateDecoder I Witness (C → Bool)) :
    BoolFn (CertificateCoordinates I T C) :=
  fun bits => (certificateInputOfBits bits).cheatSheet S decode

theorem certificateBoolFn_eq_true_iff {I : Type w} {T : Type u} {C : Type z}
    {Witness : Type v} (S : CertificateSystem (T → Bool) Witness)
    (decode : CertificateDecoder I Witness (C → Bool))
    (bits : CertificateCoordinates I T C → Bool) :
    certificateBoolFn S decode bits = true ↔
      ∃ address, (decode (fun c => bits (.inr (address, c)))).1 = true ∧
        ∀ i, S.valid (fun t => bits (.inl (i, t))) (address i)
          ((decode (fun c => bits (.inr (address, c)))).2 i) := by
  simp [certificateBoolFn, CertificateInput.AcceptsAt, certificateInputOfBits]

/-- A surjective decoder and one certified tuple supply inputs of both
output values, so this totalization cannot collapse to a constant. -/
theorem certificateBoolFn_has_zero_and_one
    {I : Type w} {T : Type u} {C : Type z} {Witness : Type v}
    (S : CertificateSystem (T → Bool) Witness)
    (decode : CertificateDecoder I Witness (C → Bool))
    (hdecode : Function.Surjective decode)
    (cores : I → T → Bool) (address : I → Bool) (witness : I → Witness)
    (hvalid : ∀ i, S.valid (cores i) (address i) (witness i)) :
    ∃ bits0 bits1,
      certificateBoolFn S decode bits0 = false ∧
      certificateBoolFn S decode bits1 = true := by
  classical
  obtain ⟨cell0, hcell0⟩ := hdecode (false, witness)
  obtain ⟨cell1, hcell1⟩ := hdecode (true, witness)
  let x : CertificateInput I (T → Bool) (C → Bool) := ⟨cores, fun _ => cell0⟩
  refine ⟨certificateBitsOfInput x,
    certificateBitsOfInput (x.plantCell address cell1), ?_, ?_⟩
  · simp only [certificateBoolFn, certificateInputOfBits_bitsOfInput]
    apply CertificateInput.zeroFlags_reject
    intro a
    exact congrArg Prod.fst hcell0
  · simp only [certificateBoolFn, certificateInputOfBits_bitsOfInput]
    exact CertificateInput.plantedCell_accepts S decode x address witness cell1 hcell1 hvalid

/-- Witnesses for the short-circuit AND--OR core: either one selected column
per row (value true), or one selected row (value false). -/
abbrev KleeneWitness (Row : Type u) (Col : Type v) := (Row → Col) ⊕ Row

def kleeneValid {Row : Type u} {Col : Type v} {Seed : Type w}
    (p : Seed → Option Bool) (x : Row → Col → Seed) (b : Bool)
    (witness : KleeneWitness Row Col) : Prop :=
  match b, witness with
  | true, .inl select => ∀ row, p (x row (select row)) = some true
  | false, .inr row => ∀ col, p (x row col) = some false
  | _, _ => False

theorem kleeneValid_compatible {Row : Type u} {Col : Type v} {Seed : Type w}
    (p : Seed → Option Bool) {x : Row → Col → Seed} {b b' : Bool}
    {witness witness' : KleeneWitness Row Col}
    (h : kleeneValid p x b witness) (h' : kleeneValid p x b' witness') : b = b' := by
  cases b <;> cases b'
  · rfl
  · cases witness with
    | inl select => exact False.elim h
    | inr row =>
      cases witness' with
      | inl select =>
        have hzero := h (select row)
        have hone := h' row
        rw [hzero] at hone
        cases hone
      | inr row' => exact False.elim h'
  · cases witness with
    | inl select =>
      cases witness' with
      | inl select' => exact False.elim h'
      | inr row =>
        have hone := h row
        have hzero := h' (select row)
        rw [hone] at hzero
        cases hzero
    | inr row => exact False.elim h
  · rfl

def kleeneCertificateSystem {Row : Type u} {Col : Type v} {Seed : Type w}
    (p : Seed → Option Bool) :
    CertificateSystem (Row → Col → Seed) (KleeneWitness Row Col) where
  valid := kleeneValid p
  compatible := kleeneValid_compatible p

theorem kleene_definedAt_true_iff {Row : Type u} {Col : Type v} {Seed : Type w}
    (p : Seed → Option Bool) (x : Row → Col → Seed) :
    (kleeneCertificateSystem p).DefinedAt x true ↔
      ∀ row, ∃ col, p (x row col) = some true := by
  classical
  constructor
  · rintro ⟨witness, hw⟩
    cases witness with
    | inl select => exact fun row => ⟨select row, hw row⟩
    | inr row => exact False.elim hw
  · intro h
    refine ⟨.inl (fun row => Classical.choose (h row)), ?_⟩
    exact fun row => Classical.choose_spec (h row)

theorem kleene_definedAt_false_iff {Row : Type u} {Col : Type v} {Seed : Type w}
    (p : Seed → Option Bool) (x : Row → Col → Seed) :
    (kleeneCertificateSystem p).DefinedAt x false ↔
      ∃ row, ∀ col, p (x row col) = some false := by
  constructor
  · rintro ⟨witness, hw⟩
    cases witness with
    | inl select => exact False.elim hw
    | inr row => exact ⟨row, hw⟩
  · rintro ⟨row, hrow⟩
    exact ⟨.inr row, hrow⟩

end QueryComplexity
