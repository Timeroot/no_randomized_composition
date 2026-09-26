import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Option
import QueryComplexity.Definitions

/-! Elementary finite weighted sums used by the direct-product argument. -/

open scoped BigOperators

namespace QueryComplexity
namespace FiniteProbability

universe u v

noncomputable def maxValue {A : Type u} [Fintype A] [Nonempty A]
    (a : A → ℝ) : ℝ :=
  a (Classical.choose (Finset.exists_max_image Finset.univ a Finset.univ_nonempty))

theorem le_maxValue {A : Type u} [Fintype A] [Nonempty A]
    (a : A → ℝ) (i : A) : a i ≤ maxValue a := by
  exact (Classical.choose_spec
    (Finset.exists_max_image Finset.univ a Finset.univ_nonempty)).2 i (Finset.mem_univ i)

theorem maxValue_le {A : Type u} [Fintype A] [Nonempty A]
    (a : A → ℝ) {b : ℝ} (h : ∀ i, a i ≤ b) : maxValue a ≤ b := by
  exact h _

theorem exists_eq_maxValue {A : Type u} [Fintype A] [Nonempty A]
    (a : A → ℝ) : ∃ i, a i = maxValue a := by
  exact ⟨_, rfl⟩

abbrev Weight (X : Type u) := X → ℝ

def mass {X : Type u} [Fintype X] (ν : Weight X) : ℝ := ∑ x, ν x

def Nonnegative {X : Type u} (ν : Weight X) : Prop := ∀ x, 0 ≤ ν x

def restrict {X : Type u} (ν : Weight X) (p : X → Bool) (b : Bool) : Weight X :=
  fun x => if p x = b then ν x else 0

theorem restrict_nonnegative {X : Type u} {ν : Weight X} (h : Nonnegative ν)
    (p : X → Bool) (b : Bool) : Nonnegative (restrict ν p b) := by
  intro x
  simp only [restrict]
  split_ifs
  · exact h x
  · exact le_rfl

theorem restrict_false_add_true {X : Type u} (ν : Weight X) (p : X → Bool) (x : X) :
    restrict ν p false x + restrict ν p true x = ν x := by
  cases h : p x <;> simp [restrict, h]

theorem mass_nonnegative {X : Type u} [Fintype X] {ν : Weight X}
    (h : Nonnegative ν) : 0 ≤ mass ν :=
  Finset.sum_nonneg fun x _ => h x

theorem mass_restrict_add {X : Type u} [Fintype X] (ν : Weight X) (p : X → Bool) :
    mass (restrict ν p false) + mass (restrict ν p true) = mass ν := by
  simp only [mass, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => restrict_false_add_true ν p x

def labelMass {X : Type u} [Fintype X] (f : X → Bool) (ν : Weight X)
    (b : Bool) : ℝ := mass (restrict ν f b)

theorem labelMass_nonnegative {X : Type u} [Fintype X] (f : X → Bool)
    {ν : Weight X} (h : Nonnegative ν) (b : Bool) : 0 ≤ labelMass f ν b :=
  mass_nonnegative (restrict_nonnegative h f b)

theorem labelMass_le_mass {X : Type u} [Fintype X] (f : X → Bool)
    {ν : Weight X} (h : Nonnegative ν) (b : Bool) : labelMass f ν b ≤ mass ν := by
  apply Finset.sum_le_sum
  intro x _
  simp only [restrict]
  split_ifs
  · exact le_rfl
  · exact h x

theorem labelMass_false_add_true {X : Type u} [Fintype X]
    (f : X → Bool) (ν : Weight X) :
    labelMass f ν false + labelMass f ν true = mass ν :=
  mass_restrict_add ν f

noncomputable def uniformWeight (X : Type u) [Fintype X] : Weight X :=
  fun _ => (Fintype.card X : ℝ)⁻¹

theorem uniformWeight_nonnegative (X : Type u) [Fintype X] :
    Nonnegative (uniformWeight X) := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)

theorem mass_uniformWeight (X : Type u) [Fintype X] [Nonempty X] :
    mass (uniformWeight X) = 1 := by
  have hc : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [mass, uniformWeight, hc]

noncomputable def pushforward {X : Type u} {Y : Type v} [Fintype X]
    (ν : Weight X) (g : X → Y) : Weight Y := by
  classical
  exact fun y => ∑ x, if g x = y then ν x else 0

theorem pushforward_nonnegative {X : Type u} {Y : Type v} [Fintype X]
    {ν : Weight X} (hν : Nonnegative ν) (g : X → Y) :
    Nonnegative (pushforward ν g) := by
  classical
  intro y
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact hν x
  · exact le_refl 0

theorem sum_pushforward_mul {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    (ν : Weight X) (g : X → Y) (h : Y → ℝ) :
    (∑ y, pushforward ν g y * h y) = ∑ x, ν x * h (g x) := by
  classical
  simp only [pushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [ite_mul, zero_mul]
  simp

theorem mass_pushforward {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    (ν : Weight X) (g : X → Y) : mass (pushforward ν g) = mass ν := by
  simpa [mass] using sum_pushforward_mul ν g (fun _ => 1)

end FiniteProbability
end QueryComplexity
