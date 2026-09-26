import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.GroupTheory.Index
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! Uniform fibers and coordinate projections of finite additive and linear maps. -/

section

/-!
# Exact privacy of finite additive cosets

These lemmas state their algebraic hypotheses explicitly.  In particular, the
surjectivity hypothesis on the observed coordinates is not an assertion that
a suitable high-distance binary code exists.
-/


universe u v w

namespace Cosets

variable {V : Type u} {W : Type v} {U : Type w}
variable [AddCommGroup V] [AddCommGroup W] [AddCommGroup U]

/-- Every requested observation can be realized without changing the syndrome. -/
def KernelProjectionSurjective (H : V →+ W) (P : V →+ U) : Prop :=
  ∀ observation, ∃ correction, H correction = 0 ∧ P correction = observation

theorem joint_surjective (H : V →+ W) (P : V →+ U)
    (hH : Function.Surjective H) (hP : KernelProjectionSurjective H P) :
    Function.Surjective (H.prod P) := by
  rintro ⟨syndrome, observation⟩
  obtain ⟨base, hbase⟩ := hH syndrome
  obtain ⟨correction, hzero, hcorrection⟩ := hP (observation - P base)
  refine ⟨base + correction, ?_⟩
  ext <;> simp [hbase, hzero, hcorrection]

/-- Translation is a bijection between any two nonempty additive fibers. -/
def fiberTranslation (H : V →+ W) (a b : W) (shift : V)
    (hshift : H shift = b - a) : {x : V // H x = a} ≃ {x : V // H x = b} where
  toFun x := ⟨x.1 + shift, by simp [x.2, hshift]⟩
  invFun x := ⟨x.1 - shift, by simp [x.2, hshift]⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

theorem fiber_card_eq (H : V →+ W) (hH : Function.Surjective H) (a b : W) :
    Nat.card {x : V // H x = a} = Nat.card {x : V // H x = b} := by
  obtain ⟨shift, hshift⟩ := hH (b - a)
  exact Nat.card_congr (fiberTranslation H a b shift hshift)

/-- The two equalities defining a joint fiber are equivalent to a product equality. -/
def jointFiberEquiv (H : V →+ W) (P : V →+ U) (syndrome : W) (observation : U) :
    {x : V // H x = syndrome ∧ P x = observation} ≃
      {x : V // (H.prod P) x = (syndrome, observation)} where
  toFun x := ⟨x.1, Prod.ext x.2.1 x.2.2⟩
  invFun x := ⟨x.1, ⟨congrArg Prod.fst x.2, congrArg Prod.snd x.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem joint_fiber_card_eq (H : V →+ W) (P : V →+ U)
    (hH : Function.Surjective H) (hP : KernelProjectionSurjective H P)
    (a b : W) (r s : U) :
    Nat.card {x : V // H x = a ∧ P x = r} =
      Nat.card {x : V // H x = b ∧ P x = s} := by
  calc
    _ = Nat.card {x : V // (H.prod P) x = (a, r)} :=
      Nat.card_congr (jointFiberEquiv H P a r)
    _ = Nat.card {x : V // (H.prod P) x = (b, s)} :=
      fiber_card_eq (H.prod P) (joint_surjective H P hH hP) _ _
    _ = _ := (Nat.card_congr (jointFiberEquiv H P b s)).symm

/-- Splitting a syndrome fiber according to its observed coordinates. -/
def fiberPartitionEquiv (H : V →+ W) (P : V →+ U) (syndrome : W) :
    (Σ observation : U, {x : V // H x = syndrome ∧ P x = observation}) ≃
      {x : V // H x = syndrome} where
  toFun x := ⟨x.2.1, x.2.2.1⟩
  invFun x := ⟨P x.1, ⟨x.1, x.2, rfl⟩⟩
  left_inv := by rintro ⟨observation, x, hH, hP⟩; cases hP; rfl
  right_inv _ := rfl

theorem joint_fiber_card_mul [Fintype V] [Fintype U]
    (H : V →+ W) (P : V →+ U)
    (hH : Function.Surjective H) (hP : KernelProjectionSurjective H P)
    (syndrome : W) (observation : U) :
    Nat.card {x : V // H x = syndrome ∧ P x = observation} * Nat.card U =
      Nat.card {x : V // H x = syndrome} := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hsplit := Fintype.card_congr (fiberPartitionEquiv H P syndrome)
  rw [Fintype.card_sigma] at hsplit
  rw [← hsplit]
  have hequal : ∀ r : U,
      Fintype.card {x : V // H x = syndrome ∧ P x = r} =
        Fintype.card {x : V // H x = syndrome ∧ P x = observation} := by
    intro r
    simpa only [Nat.card_eq_fintype_card] using
      joint_fiber_card_eq H P hH hP syndrome syndrome r observation
  simp_rw [hequal]
  simp [mul_comm]

/-- Under the uniform law on any syndrome fiber, every observation is equally likely. -/
theorem uniform_observation_probability [Fintype V] [Fintype U]
    (H : V →+ W) (P : V →+ U)
    (hH : Function.Surjective H) (hP : KernelProjectionSurjective H P)
    (syndrome : W) (observation : U) :
    (Nat.card {x : V // H x = syndrome ∧ P x = observation} : ℝ) /
        (Nat.card {x : V // H x = syndrome} : ℝ) =
      1 / (Nat.card U : ℝ) := by
  have hU : (Nat.card U : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := U)).ne'
  have hF : (Nat.card {x : V // H x = syndrome} : ℝ) ≠ 0 := by
    obtain ⟨x, hx⟩ := hH syndrome
    letI : Nonempty {x : V // H x = syndrome} := ⟨⟨x, hx⟩⟩
    exact_mod_cast (Nat.card_pos (α := {x : V // H x = syndrome})).ne'
  apply (div_eq_div_iff hF hU).2
  norm_cast
  simpa using joint_fiber_card_mul H P hH hP syndrome observation

end Cosets

namespace Cosets

section LinearProjection

variable {K : Type*} [Field K]
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {W : Type*} [AddCommGroup W] [Module K W]

/-- Restriction to the queried coordinate set. -/
def restrictCoordinates (s : Finset J) : (J → K) →ₗ[K] (s → K) where
  toFun x j := x j.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype J] in
theorem restrictCoordinates_surjective (s : Finset J) :
    Function.Surjective (restrictCoordinates (K := K) s) := by
  intro y
  refine ⟨fun j => if h : j ∈ s then y ⟨j, h⟩ else 0, ?_⟩
  ext j
  simp [restrictCoordinates, j.2]

/-- Support of the coefficient vector of a linear functional. -/
noncomputable def dualSupport (f : Module.Dual K (J → K)) : Finset J := by
  classical
  exact Finset.univ.filter (fun j => f (Pi.single j 1) ≠ 0)

theorem restricted_dual_support_subset (s : Finset J)
    (f : Module.Dual K (s → K)) :
    dualSupport (f.comp (restrictCoordinates s)) ⊆ s := by
  classical
  intro j hj
  by_contra hjs
  have hzero : restrictCoordinates (K := K) s (Pi.single j 1) = 0 := by
    ext i
    have hne : i.1 ≠ j := by intro heq; exact hjs (heq ▸ i.2)
    simp [restrictCoordinates, hne]
  have hnonzero : f (restrictCoordinates s (Pi.single j 1)) ≠ 0 := by
    simpa [dualSupport] using hj
  exact hnonzero (by rw [hzero]; simp)

/-- A dual functional supported on too few queried coordinates must be zero. -/
theorem supported_dual_eq_zero (H : (J → K) →ₗ[K] W)
    (d : ℕ)
    (hd : ∀ f : Module.Dual K W,
      f.comp H ≠ 0 → d ≤ (dualSupport (f.comp H)).card)
    (s : Finset J) (hs : s.card < d)
    (f : Module.Dual K W)
    (hf : dualSupport (f.comp H) ⊆ s) : f.comp H = 0 := by
  by_contra hnonzero
  have hle := (hd f hnonzero).trans (Finset.card_le_card hf)
  exact (Nat.not_le_of_lt hs) hle

/-- Rowspace distance implies that any values on fewer than `d` coordinates
can be attained by a vector in the kernel. -/
theorem kernelProjectionSurjective_of_dual_distance
    (H : (J → K) →ₗ[K] W) (d : ℕ)
    (hd : ∀ f : Module.Dual K W,
      f.comp H ≠ 0 → d ≤ (dualSupport (f.comp H)).card)
    (s : Finset J) (hs : s.card < d) :
    KernelProjectionSurjective H.toAddMonoidHom
      (restrictCoordinates (K := K) s).toAddMonoidHom := by
  let P := restrictCoordinates (K := K) s
  let Q := P.comp H.ker.subtype
  have hQ : Function.Surjective Q := by
    apply LinearMap.dualMap_injective_iff.mp
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro f hf
    have hann : f.comp P ∈ H.ker.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro x hx
      have h := LinearMap.congr_fun hf (⟨x, hx⟩ : H.ker)
      exact h
    rw [← H.range_dualMap_eq_dualAnnihilator_ker] at hann
    obtain ⟨g, hg⟩ := hann
    have hg' : g.comp H = f.comp P := hg
    have hsupport : dualSupport (g.comp H) ⊆ s := by
      rw [hg']
      exact restricted_dual_support_subset s f
    have hzero := supported_dual_eq_zero H d hd s hs g hsupport
    have hfP : f.comp P = 0 := hg' ▸ hzero
    apply LinearMap.dualMap_injective_of_surjective
      (restrictCoordinates_surjective (K := K) s)
    exact hfP
  intro observation
  obtain ⟨x, hx⟩ := hQ observation
  exact ⟨x.1, x.2, hx⟩

/-- Positive distance for every nonzero combination of the rows also supplies
the required full-row-rank property. -/
theorem surjective_of_nonzero_dual_distance
    (H : (J → K) →ₗ[K] W) (d : ℕ) (hdpos : 0 < d)
    (hd : ∀ f : Module.Dual K W,
      f ≠ 0 → d ≤ (dualSupport (f.comp H)).card) :
    Function.Surjective H := by
  apply LinearMap.dualMap_injective_iff.mp
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  by_contra hfnonzero
  have hle := hd f hfnonzero
  have hf' : f.comp H = 0 := hf
  rw [hf'] at hle
  have hle' : d ≤ 0 := by simpa [dualSupport] using hle
  exact Nat.not_le_of_lt hdpos hle'

/-- Exact uniform privacy from a single explicit minimum-distance condition.
This theorem applies, in particular, to finite binary matrices. -/
theorem uniform_coordinates_of_dual_distance [Fintype K]
    (H : (J → K) →ₗ[K] W) (d : ℕ) (hdpos : 0 < d)
    (hd : ∀ f : Module.Dual K W,
      f ≠ 0 → d ≤ (dualSupport (f.comp H)).card)
    (s : Finset J) (hs : s.card < d)
    (syndrome : W) (observation : s → K) :
    (Nat.card {x : J → K // H x = syndrome ∧
        restrictCoordinates s x = observation} : ℝ) /
        (Nat.card {x : J → K // H x = syndrome} : ℝ) =
      1 / (Nat.card (s → K) : ℝ) := by
  have hd' : ∀ f : Module.Dual K W,
      f.comp H ≠ 0 → d ≤ (dualSupport (f.comp H)).card := by
    intro f hf
    apply hd f
    intro hzero
    apply hf
    simp [hzero]
  exact uniform_observation_probability H.toAddMonoidHom
    (restrictCoordinates s).toAddMonoidHom
    (surjective_of_nonzero_dual_distance H d hdpos hd)
    (kernelProjectionSurjective_of_dual_distance H d hd' s hs)
    syndrome observation

end LinearProjection

end Cosets

end

section

/-!
# Counting bad images under a uniform surjective additive map

The exact identities here are finite counting statements. They justify
the probability calculation used in the random-matrix construction without
postulating a distributional uniformity or a code-existence theorem.
-/

namespace Cosets

universe u v

variable {X : Type u} {Y : Type v}
variable [AddCommGroup X] [AddCommGroup Y] [Fintype X] [Fintype Y]

theorem surjective_fiber_card_mul
    (F : X →+ Y) (hF : Function.Surjective F) (y : Y) :
    Nat.card {x : X // F x = y} * Nat.card Y = Nat.card X := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hsplit := Fintype.card_congr (Equiv.sigmaFiberEquiv F)
  rw [Fintype.card_sigma] at hsplit
  rw [← hsplit]
  have hequal : ∀ z : Y, Fintype.card {x : X // F x = z} =
      Fintype.card {x : X // F x = y} := by
    intro z
    simpa only [Nat.card_eq_fintype_card] using fiber_card_eq F hF z y
  simp_rw [hequal]
  simp [mul_comm]

/-- A preimage is partitioned into the fibers over the selected images. -/
def preimagePartitionEquiv (F : X →+ Y) (bad : Finset Y) :
    (Σ y : bad, {x : X // F x = y.1}) ≃ {x : X // F x ∈ bad} where
  toFun x := ⟨x.2.1, by rw [x.2.2]; exact x.1.2⟩
  invFun x := ⟨⟨F x.1, x.2⟩, ⟨x.1, rfl⟩⟩
  left_inv := by rintro ⟨⟨y, hy⟩, x, hx⟩; cases hx; rfl
  right_inv _ := rfl

omit [Fintype Y] in
theorem bad_preimage_card_eq_fiber
    (F : X →+ Y) (hF : Function.Surjective F) (bad : Finset Y) (y : Y) :
    Nat.card {x : X // F x ∈ bad} =
      bad.card * Nat.card {x : X // F x = y} := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hsplit := Fintype.card_congr (preimagePartitionEquiv F bad)
  rw [Fintype.card_sigma] at hsplit
  rw [← hsplit]
  have hequal : ∀ z : bad, Fintype.card {x : X // F x = z.1} =
      Fintype.card {x : X // F x = y} := by
    intro z
    simpa only [Nat.card_eq_fintype_card] using fiber_card_eq F hF z.1 y
  simp_rw [hequal]
  simp

/-- Exact finite form of `Pr[F x ∈ bad] = |bad| / |Y|`. -/
theorem bad_preimage_card_mul
    (F : X →+ Y) (hF : Function.Surjective F) (bad : Finset Y) :
    Nat.card {x : X // F x ∈ bad} * Nat.card Y = bad.card * Nat.card X := by
  rw [bad_preimage_card_eq_fiber F hF bad (0 : Y), mul_assoc,
    surjective_fiber_card_mul F hF]

/-- The elementary probabilistic method for a finite family of uniform images:
if the union bound is strictly below one, some input avoids every bad event. -/
theorem exists_avoiding_bad_images {I : Type*} [Fintype I]
    (F : I → X →+ Y) (hF : ∀ i, Function.Surjective (F i))
    (bad : Finset Y) (hsmall : Nat.card I * bad.card < Nat.card Y) :
    ∃ x : X, ∀ i, F i x ∉ bad := by
  classical
  let A : I → Finset X := fun i => Finset.univ.filter (fun x => F i x ∈ bad)
  let badUnion : Finset X := Finset.univ.biUnion A
  have hcard : ∀ i, (A i).card * Fintype.card Y = bad.card * Fintype.card X := by
    intro i
    simpa [A, Nat.card_eq_fintype_card, Fintype.card_subtype] using
      bad_preimage_card_mul (F i) (hF i) bad
  have hsmall' : Fintype.card I * bad.card < Fintype.card Y := by
    simpa only [Nat.card_eq_fintype_card] using hsmall
  have hmul : badUnion.card * Fintype.card Y < Fintype.card X * Fintype.card Y := by
    calc
      badUnion.card * Fintype.card Y ≤
          (∑ i, (A i).card) * Fintype.card Y :=
        Nat.mul_le_mul_right _ Finset.card_biUnion_le
      _ = ∑ i, (A i).card * Fintype.card Y := by rw [Finset.sum_mul]
      _ = Fintype.card I * (bad.card * Fintype.card X) := by simp_rw [hcard]; simp
      _ < Fintype.card X * Fintype.card Y := by
        have := Nat.mul_lt_mul_of_pos_right hsmall' (Fintype.card_pos (α := X))
        simpa [mul_assoc, mul_comm, mul_left_comm] using this
  by_contra! hcover
  have hfull : badUnion = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨i, hi⟩ := hcover x
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [A, hi]⟩
  simp [hfull] at hmul

end Cosets

end
