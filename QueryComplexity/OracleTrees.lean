import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

namespace QueryComplexity

universe u v w

/-- A deterministic query tree with a finite, possibly non-Boolean answer alphabet. -/
inductive OracleTree (Coordinate : Type u) (Answer : Type v) (Output : Type w) where
  | leaf (output : Output)
  | query (coordinate : Coordinate) (next : Answer → OracleTree Coordinate Answer Output)

namespace OracleTree

variable {Coordinate : Type u} {Answer : Type v} {Output : Type w}

def eval : OracleTree Coordinate Answer Output → (Coordinate → Answer) → Output
  | .leaf output, _ => output
  | .query coordinate next, x => (next (x coordinate)).eval x

def depth [Fintype Answer] : OracleTree Coordinate Answer Output → ℕ
  | .leaf _ => 0
  | .query _ next => 1 + Finset.univ.sup (fun answer => (next answer).depth)

/-- Leaves retain the complete adaptive sequence of branch answers. -/
def Leaf : OracleTree Coordinate Answer Output → Type v
  | .leaf _ => PUnit
  | .query _ next => Σ answer : Answer, (next answer).Leaf

instance leafFintype [Fintype Answer] :
    (tree : OracleTree Coordinate Answer Output) → Fintype tree.Leaf
  | .leaf _ => by change Fintype PUnit; infer_instance
  | .query _ next => by
    change Fintype (Σ answer : Answer, (next answer).Leaf)
    letI : ∀ answer, Fintype (next answer).Leaf := fun answer => leafFintype (next answer)
    exact inferInstance

def route : (tree : OracleTree Coordinate Answer Output) → (Coordinate → Answer) → tree.Leaf
  | .leaf _, _ => PUnit.unit
  | .query coordinate next, x => ⟨x coordinate, (next (x coordinate)).route x⟩

def transcript : (tree : OracleTree Coordinate Answer Output) → tree.Leaf → List (Coordinate × Answer)
  | .leaf _, _ => []
  | .query coordinate next, path => (coordinate, path.1) :: (next path.1).transcript path.2

def Matches (trace : List (Coordinate × Answer)) (x : Coordinate → Answer) : Prop :=
  ∀ pair ∈ trace, x pair.1 = pair.2

@[simp] theorem matches_nil (x : Coordinate → Answer) : Matches [] x := by simp [Matches]

@[simp] theorem matches_cons (coordinate : Coordinate) (answer : Answer)
    (trace : List (Coordinate × Answer)) (x : Coordinate → Answer) :
    Matches ((coordinate, answer) :: trace) x ↔ x coordinate = answer ∧ Matches trace x := by
  simp [Matches]

theorem route_eq_iff : ∀ (tree : OracleTree Coordinate Answer Output)
    (leaf : tree.Leaf) (x : Coordinate → Answer),
    tree.route x = leaf ↔ Matches (tree.transcript leaf) x := by
  intro tree
  induction tree with
  | leaf output =>
    intro leaf x
    cases leaf
    simp [route, transcript]
  | query coordinate next ih =>
    rintro ⟨answer, leaf⟩ x
    simp only [transcript, matches_cons]
    constructor
    · intro h
      have hx : x coordinate = answer := congrArg Sigma.fst h
      refine ⟨hx, ?_⟩
      cases hx
      have htail : (next (x coordinate)).route x = leaf :=
        eq_of_heq (Sigma.mk.inj_iff.mp h).2
      exact (ih (x coordinate) leaf x).1 htail
    · rintro ⟨hx, hrest⟩
      cases hx
      have htail := (ih (x coordinate) leaf x).2 hrest
      change (⟨x coordinate, (next (x coordinate)).route x⟩ : Σ a, (next a).Leaf) =
        ⟨x coordinate, leaf⟩
      rw [htail]

theorem route_matches (tree : OracleTree Coordinate Answer Output) (x : Coordinate → Answer) :
    Matches (tree.transcript (tree.route x)) x := (route_eq_iff tree _ x).1 rfl

theorem transcript_length_le_depth [Fintype Answer] :
    ∀ (tree : OracleTree Coordinate Answer Output) (leaf : tree.Leaf),
      (tree.transcript leaf).length ≤ tree.depth := by
  intro tree
  induction tree with
  | leaf output => intro leaf; simp [transcript, depth]
  | query coordinate next ih =>
    rintro ⟨answer, leaf⟩
    have hbranch : (next answer).depth ≤ Finset.univ.sup (fun a => (next a).depth) :=
      Finset.le_sup (f := fun a : Answer => (next a).depth) (Finset.mem_univ answer)
    simp only [transcript, List.length_cons, depth]
    have := (ih answer leaf).trans hbranch
    omega

def queried [DecidableEq Coordinate] (tree : OracleTree Coordinate Answer Output) (leaf : tree.Leaf) :
    Finset Coordinate := ((tree.transcript leaf).map Prod.fst).toFinset

theorem route_eq_reference_iff [DecidableEq Coordinate]
    (tree : OracleTree Coordinate Answer Output) (reference x : Coordinate → Answer) :
    tree.route x = tree.route reference ↔
      ∀ coordinate ∈ tree.queried (tree.route reference), x coordinate = reference coordinate := by
  rw [route_eq_iff]
  have href := route_matches tree reference
  constructor
  · intro hx coordinate hmem
    obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hmem)
    exact (hx pair hpair).trans (href pair hpair).symm
  · intro hx pair hpair
    have hmem : pair.1 ∈ tree.queried (tree.route reference) :=
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨pair, hpair, rfl⟩)
    exact (hx pair.1 hmem).trans (href pair hpair)

theorem queried_card_le_depth [Fintype Answer] [DecidableEq Coordinate]
    (tree : OracleTree Coordinate Answer Output) (leaf : tree.Leaf) :
    (tree.queried leaf).card ≤ tree.depth := by
  have h := List.toFinset_card_le ((tree.transcript leaf).map Prod.fst)
  simp only [List.length_map] at h
  exact h.trans (transcript_length_le_depth tree leaf)

end OracleTree

end QueryComplexity
