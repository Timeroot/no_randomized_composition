import QueryComplexity.Cosets

/-!
# Counting bad images under a uniform surjective additive map

The exact identities here are finite counting statements. They justify
the probability calculation used in the random-matrix construction without
postulating a distributional uniformity or a code-existence theorem.
-/

namespace QueryComplexity.Cosets

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

theorem bad_preimage_probability
    (F : X →+ Y) (hF : Function.Surjective F) (bad : Finset Y) :
    (Nat.card {x : X // F x ∈ bad} : ℝ) / (Nat.card X : ℝ) =
      (bad.card : ℝ) / (Nat.card Y : ℝ) := by
  have hX : (Nat.card X : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := X)).ne'
  have hY : (Nat.card Y : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Y)).ne'
  apply (div_eq_div_iff hX hY).2
  exact_mod_cast bad_preimage_card_mul F hF bad

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

end QueryComplexity.Cosets
