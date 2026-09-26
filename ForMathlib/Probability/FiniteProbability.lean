import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Fintype.Pi

/-! Finite weighted sums, pushforwards, uniform averages, and resampling identities. -/

section

/-! Elementary finite weighted sums, restrictions, and pushforwards. -/

open scoped BigOperators

namespace FiniteProbability

universe u v

/-- The maximum of a nonempty finite family in any linear order. -/
noncomputable def maxValue {A : Type u} {B : Type v} [Fintype A] [Nonempty A]
    [LinearOrder B] (a : A → B) : B :=
  a (Classical.choose (Finset.exists_max_image Finset.univ a Finset.univ_nonempty))

theorem le_maxValue {A : Type u} {B : Type v} [Fintype A] [Nonempty A]
    [LinearOrder B] (a : A → B) (i : A) : a i ≤ maxValue a := by
  exact (Classical.choose_spec
    (Finset.exists_max_image Finset.univ a Finset.univ_nonempty)).2 i (Finset.mem_univ i)

theorem maxValue_le {A : Type u} {B : Type v} [Fintype A] [Nonempty A]
    [LinearOrder B] (a : A → B) {b : B} (h : ∀ i, a i ≤ b) : maxValue a ≤ b := by
  exact h _

theorem exists_eq_maxValue {A : Type u} {B : Type v} [Fintype A] [Nonempty A]
    [LinearOrder B] (a : A → B) : ∃ i, a i = maxValue a := by
  exact ⟨_, rfl⟩

abbrev Weight (X : Type u) := X → ℝ

def mass {X : Type u} [Fintype X] (ν : Weight X) : ℝ := ∑ x, ν x

def Nonnegative {X : Type u} (ν : Weight X) : Prop := ∀ x, 0 ≤ ν x

def restrict {X : Type u} {Y : Type v} [DecidableEq Y]
    (ν : Weight X) (p : X → Y) (b : Y) : Weight X :=
  fun x => if p x = b then ν x else 0

theorem restrict_nonnegative {X : Type u} {Y : Type v} [DecidableEq Y]
    {ν : Weight X} (h : Nonnegative ν) (p : X → Y) (b : Y) :
    Nonnegative (restrict ν p b) := by
  intro x
  exact ite_nonneg (h x) le_rfl

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

def labelMass {X : Type u} {Y : Type v} [Fintype X] [DecidableEq Y]
    (f : X → Y) (ν : Weight X) (b : Y) : ℝ := mass (restrict ν f b)

theorem labelMass_nonnegative {X : Type u} {Y : Type v} [Fintype X] [DecidableEq Y]
    (f : X → Y) {ν : Weight X} (h : Nonnegative ν) (b : Y) : 0 ≤ labelMass f ν b :=
  mass_nonnegative (restrict_nonnegative h f b)

theorem labelMass_le_mass {X : Type u} {Y : Type v} [Fintype X] [DecidableEq Y]
    (f : X → Y) {ν : Weight X} (h : Nonnegative ν) (b : Y) : labelMass f ν b ≤ mass ν := by
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hx : f x = b <;> simp [restrict, hx, h x]

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
  exact fun _ => Finset.sum_nonneg fun x _ => ite_nonneg (hν x) le_rfl

theorem sum_pushforward_mul {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    (ν : Weight X) (g : X → Y) (h : Y → ℝ) :
    (∑ y, pushforward ν g y * h y) = ∑ x, ν x * h (g x) := by
  classical
  simp only [pushforward, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

theorem mass_pushforward {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    (ν : Weight X) (g : X → Y) : mass (pushforward ν g) = mass ν := by
  simpa [mass] using sum_pushforward_mul ν g (fun _ => 1)

/-- Restricting an event after a pushforward is the same as pulling it back. -/
theorem sum_pushforward_event {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    (ν : Weight X) (g : X → Y) (p : Y → Prop) [DecidablePred p] :
    (∑ y, if p y then pushforward ν g y else 0) =
      ∑ x, if p (g x) then ν x else 0 := by
  simpa only [mul_ite, mul_one, mul_zero] using
    sum_pushforward_mul ν g (fun y => if p y then 1 else 0)

/-- A probability-weighted average only needs a bound on the support. -/
theorem sum_mul_le_of_mass_one {X : Type u} [Fintype X] {ν : Weight X}
    (hν : Nonnegative ν) (hmass : mass ν = 1) {f : X → ℝ} {M : ℝ}
    (h : ∀ x, ν x ≠ 0 → f x ≤ M) : (∑ x, ν x * f x) ≤ M := by
  calc
    _ ≤ ∑ x, ν x * M := Finset.sum_le_sum fun x _ => by
      by_cases hx : ν x = 0
      · simp [hx]
      · exact mul_le_mul_of_nonneg_left (h x hx) (hν x)
    _ = M := by simpa only [mass, Finset.sum_mul, one_mul] using congrArg (· * M) hmass

/-- An event under a uniform pushforward has its ordinary finite counting probability. -/
theorem uniform_pushforward_event {A B : Type*} [Fintype A] [Fintype B]
    (mapping : A → B) (event : B → Prop) [DecidablePred event] :
    (∑ b, if event b then pushforward (uniformWeight A) mapping b else 0) =
      (Nat.card {a : A // event (mapping a)} : ℝ) / Nat.card A := by
  classical
  rw [sum_pushforward_event]
  simp [uniformWeight, ← Finset.sum_filter, Nat.card_eq_fintype_card, Fintype.card_subtype,
    div_eq_mul_inv]

/-- The optimal equal-prior binary decision advantage is bounded by one
quarter of the L1 distance. This applies to any deterministic transcript rule. -/
theorem binary_success_le_l1 {X : Type*} [Fintype X] (μ₀ μ₁ : X → ℝ)
    (hmass₀ : ∑ t, μ₀ t = 1) (hmass₁ : ∑ t, μ₁ t = 1)
    (answer : X → Bool) :
    (1 : ℝ) / 2 * (∑ t, if answer t then μ₁ t else μ₀ t) ≤
      1 / 2 + 1 / 4 * ∑ t, |μ₁ t - μ₀ t| := by
  have hpoint : ∀ t, (if answer t then μ₁ t else μ₀ t) ≤
      (μ₀ t + μ₁ t + |μ₁ t - μ₀ t|) / 2 := by
    intro t
    have h₁ := le_abs_self (μ₁ t - μ₀ t)
    have h₀ := neg_le_abs (μ₁ t - μ₀ t)
    cases answer t <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  have hsum := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset X)) => hpoint t)
  simp only [← Finset.sum_div, Finset.sum_add_distrib, hmass₀, hmass₁] at hsum
  linarith


end FiniteProbability

end

section

open scoped BigOperators

namespace FiniteProbability

def resampleSwap {I T : Type*} [DecidableEq I] (i : I) :
    ((I → T) × T) ≃ ((I → T) × T) where
  toFun p := (Function.update p.1 i p.2, p.1 i)
  invFun p := (Function.update p.1 i p.2, p.1 i)
  left_inv p := by
    ext j
    · by_cases hj : j = i <;> simp [hj]
    · simp
  right_inv p := by
    ext j
    · by_cases hj : j = i <;> simp [hj]
    · simp

theorem sum_resample {I T M : Type*} [Fintype I] [DecidableEq I] [Fintype T]
    [AddCommMonoid M] (i : I) (f : (I → T) → M) :
    (∑ a : I → T, ∑ t : T, f (Function.update a i t)) =
      Fintype.card T • ∑ a : I → T, f a := by
  classical
  have h := (resampleSwap (T := T) i).sum_comp (fun p : (I → T) × T => f p.1)
  simpa [resampleSwap, Fintype.sum_prod_type, Finset.smul_sum] using h

end FiniteProbability

end

section

open scoped BigOperators

namespace FiniteProbability

universe u v

noncomputable def average {X : Type u} [Fintype X] (f : X → ℝ) : ℝ :=
  ∑ x, uniformWeight X x * f x

theorem average_const {X : Type u} [Fintype X] [Nonempty X] (c : ℝ) :
    average (fun _ : X => c) = c := by
  simpa only [average, mass, ← Finset.sum_mul, one_mul] using
    congrArg (· * c) (mass_uniformWeight X)

theorem average_le {X : Type u} [Fintype X] {f g : X → ℝ} (h : ∀ x, f x ≤ g x) :
    average f ≤ average g := Finset.sum_le_sum fun x _ =>
  mul_le_mul_of_nonneg_left (h x) (uniformWeight_nonnegative X x)

theorem average_add {X : Type u} [Fintype X] (f g : X → ℝ) :
    average (fun x => f x + g x) = average f + average g := by
  simp only [average, mul_add, Finset.sum_add_distrib]

theorem average_mul {X : Type u} [Fintype X] (c : ℝ) (f : X → ℝ) :
    average (fun x => c * f x) = c * average f := by
  simp only [average, Finset.mul_sum, mul_left_comm]

theorem average_div {X : Type u} [Fintype X] (f : X → ℝ) (c : ℝ) :
    average (fun x => f x / c) = average f / c := by
  simpa only [div_eq_mul_inv, mul_comm] using average_mul c⁻¹ f

theorem average_sum {X : Type u} {J : Type v} [Fintype X] [Fintype J]
    (f : J → X → ℝ) : average (fun x => ∑ j, f j x) = ∑ j, average (f j) := by
  simp only [average, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem average_equiv {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (f : Y → ℝ) : average (fun x => f (e x)) = average f := by
  simp only [average, uniformWeight, ← Finset.mul_sum]
  rw [Fintype.card_congr e, e.sum_comp]

theorem average_prod {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    (f : X × Y → ℝ) : average f = average (fun x => average (fun y => f (x, y))) := by
  simp only [average, uniformWeight, Fintype.sum_prod_type, Finset.mul_sum,
    Fintype.card_prod, Nat.cast_mul, mul_inv, mul_assoc]

theorem average_comm {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    (f : X → Y → ℝ) :
    average (fun x => average (fun y => f x y)) = average (fun y => average (fun x => f x y)) := by
  simp only [average, Finset.mul_sum, mul_left_comm]
  rw [Finset.sum_comm]

theorem average_resample {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [Nonempty X] (i : I) (f : (I → X) → ℝ) :
    average (fun a => average (fun x => f (Function.update a i x))) = average f := by
  rw [← average_prod (fun p : (I → X) × X => f (Function.update p.1 i p.2))]
  have he := average_equiv (resampleSwap (T := X) i) (fun p : (I → X) × X => f p.1)
  simpa only [resampleSwap, Equiv.coe_fn_mk, average_prod, average_const] using he

end FiniteProbability

end
