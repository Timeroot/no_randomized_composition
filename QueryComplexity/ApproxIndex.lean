import QueryComplexity.Definitions
import Mathlib.Tactic

/-! The partial approximate-index seed, represented on an actual finite
Boolean cube. An entry consists of a presence bit and a value bit. The value
bit at an erased entry is immaterial. The radius is a natural parameter;
the probabilistic bounds will impose the desired relation to `k`. -/

namespace QueryComplexity

abbrev ApproxIndexCoordinates (k : ℕ) :=
  Fin k ⊕ ((Fin k → Bool) × Bool)

namespace ApproxIndex

def address {k : ℕ} (x : ApproxIndexCoordinates k → Bool) : Fin k → Bool :=
  fun i => x (.inl i)

def present {k : ℕ} (x : ApproxIndexCoordinates k → Bool) (a : Fin k → Bool) : Bool :=
  x (.inr (a, false))

def entry {k : ℕ} (x : ApproxIndexCoordinates k → Bool) (a : Fin k → Bool) : Bool :=
  x (.inr (a, true))

def distance {k : ℕ} (a b : Fin k → Bool) : ℕ :=
  (Finset.univ.filter (fun i => a i ≠ b i)).card

@[simp] theorem distance_self {k : ℕ} (a : Fin k → Bool) : distance a a = 0 := by
  simp [distance]

theorem distance_comm {k : ℕ} (a b : Fin k → Bool) : distance a b = distance b a := by
  simp only [distance, ne_comm]

theorem distance_le {k : ℕ} (a b : Fin k → Bool) : distance a b ≤ k := by
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- A valid seed has one common bit throughout the ball and erasures outside. -/
def Valid {k : ℕ} (radius : ℕ) (x : ApproxIndexCoordinates k → Bool) (z : Bool) : Prop :=
  (∀ a, present x a = decide (distance (address x) a ≤ radius)) ∧
    ∀ a, distance (address x) a ≤ radius → entry x a = z

/-- Every valid seed reveals its value at its own address. -/
theorem entry_address {k radius : ℕ} {x : ApproxIndexCoordinates k → Bool} {z : Bool}
    (h : Valid radius x z) : entry x (address x) = z :=
  h.2 _ (by simp)

theorem valid_unique {k radius : ℕ} {x : ApproxIndexCoordinates k → Bool} {z z' : Bool}
    (h : Valid radius x z) (h' : Valid radius x z') : z = z' :=
  (entry_address h).symm.trans (entry_address h')

noncomputable def value {k : ℕ} (radius : ℕ)
    (x : ApproxIndexCoordinates k → Bool) : Option Bool := by
  classical
  exact if Valid radius x (entry x (address x))
    then some (entry x (address x)) else none

theorem value_eq_some_iff {k : ℕ} (radius : ℕ)
    (x : ApproxIndexCoordinates k → Bool) (z : Bool) :
    value radius x = some z ↔ Valid radius x z := by
  classical
  constructor
  · intro h
    unfold value at h
    split_ifs at h with hv
    · cases Option.some.inj h
      exact hv
  · intro h
    have he := entry_address h
    simp [value, he, h]

/-- A canonical input for every address and output bit. -/
def encode {k : ℕ} (radius : ℕ) (a : Fin k → Bool) (z : Bool) :
    ApproxIndexCoordinates k → Bool
  | .inl i => a i
  | .inr (b, false) => decide (distance a b ≤ radius)
  | .inr (b, true) => if distance a b ≤ radius then z else false

@[simp] theorem address_encode {k : ℕ} (radius : ℕ) (a : Fin k → Bool) (z : Bool) :
    address (encode radius a z) = a := rfl

theorem valid_encode {k : ℕ} (radius : ℕ) (a : Fin k → Bool) (z : Bool) :
    Valid radius (encode radius a z) z := by
  constructor
  · intro b
    rfl
  · intro b hb
    simpa only [address_encode, entry, encode, if_pos] using
      (if_pos hb : (if distance a b ≤ radius then z else false) = z)

@[simp] theorem value_encode {k : ℕ} (radius : ℕ) (a : Fin k → Bool) (z : Bool) :
    value radius (encode radius a z) = some z :=
  (value_eq_some_iff radius _ z).2 (valid_encode radius a z)

/-- The deterministic extension used for the coarse core upper bound. -/
def extension {k : ℕ} : BoolFn (ApproxIndexCoordinates k) :=
  fun x => entry x (address x)

theorem extension_correct {k : ℕ} (radius : ℕ)
    (x : ApproxIndexCoordinates k → Bool) (z : Bool)
    (h : value radius x = some z) : extension x = z :=
  entry_address ((value_eq_some_iff radius x z).1 h)

end ApproxIndex
end QueryComplexity
