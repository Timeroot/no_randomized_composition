import QueryComplexity.ApproxIndexLower

/-! Elementary fourth moments for uniform Boolean addresses conditioned on a
query transcript. This file uses finite sums and a coordinate-flip involution. -/

open scoped BigOperators

namespace QueryComplexity.ApproxIndex

open FiniteProbability

variable {k : ℕ}

def knownCoordinates (trace : AddressTrace k) : Finset (Fin k) :=
  (trace.map Prod.fst).toFinset

theorem knownCoordinates_card_le (trace : AddressTrace k) :
    (knownCoordinates trace).card ≤ trace.length := by
  simpa [knownCoordinates] using List.toFinset_card_le (trace.map Prod.fst)

def flipAddress (i : Fin k) (a : Fin k → Bool) : Fin k → Bool :=
  Function.update a i (!(a i))

theorem flipAddress_involutive (i : Fin k) : Function.Involutive (flipAddress i) := by
  intro a
  funext j
  by_cases hj : j = i
  · subst j
    simp [flipAddress]
  · simp [flipAddress, hj]

def flipEquiv (i : Fin k) : (Fin k → Bool) ≃ (Fin k → Bool) where
  toFun := flipAddress i
  invFun := flipAddress i
  left_inv := flipAddress_involutive i
  right_inv := flipAddress_involutive i

theorem sliceWeight_flip (trace : AddressTrace k) (i : Fin k)
    (hi : i ∉ knownCoordinates trace) (a : Fin k → Bool) :
    sliceWeight trace (flipAddress i a) = sliceWeight trace a := by
  have hpi (p : Fin k × Bool) (hp : p ∈ trace) : p.1 ≠ i := by
    intro he
    apply hi
    simp only [knownCoordinates, List.mem_toFinset, List.mem_map]
    exact ⟨p, hp, he⟩
  have he : traceMatches trace (flipAddress i a) ↔ traceMatches trace a := by
    unfold traceMatches
    apply forall_congr'
    intro p
    apply forall_congr'
    intro hp
    simp [flipAddress, hpi p hp]
  simp only [sliceWeight, he]

def agreement (a b : Fin k → Bool) (i : Fin k) : ℝ :=
  if a i = b i then 1 else -1

theorem agreement_sq (a b : Fin k → Bool) (i : Fin k) : agreement a b i ^ 2 = 1 := by
  simp only [agreement]
  split_ifs <;> norm_num

theorem agreement_cube (a b : Fin k → Bool) (i : Fin k) :
    agreement a b i ^ 3 = agreement a b i := by
  simp only [agreement]
  split_ifs <;> norm_num

theorem agreement_fourth (a b : Fin k → Bool) (i : Fin k) : agreement a b i ^ 4 = 1 := by
  simp only [agreement]
  split_ifs <;> norm_num

theorem agreement_flip (a b : Fin k → Bool) (i : Fin k) :
    agreement (flipAddress i a) b i = -agreement a b i := by
  simp only [agreement, flipAddress, Function.update_self]
  cases a i <;> cases b i <;> norm_num

def signedSum (b : Fin k → Bool) (s : Finset (Fin k)) (a : Fin k → Bool) : ℝ :=
  ∑ i ∈ s, agreement a b i

theorem signedSum_flip (b : Fin k → Bool) (s : Finset (Fin k)) (i : Fin k)
    (hi : i ∉ s) (a : Fin k → Bool) : signedSum b s (flipAddress i a) = signedSum b s a := by
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≠ i := by intro he; subst j; exact hi hj
  simp [agreement, flipAddress, hji]

theorem signedSum_insert (b : Fin k → Bool) (s : Finset (Fin k)) (i : Fin k)
    (hi : i ∉ s) (a : Fin k → Bool) :
    signedSum b (insert i s) a = agreement a b i + signedSum b s a := by
  exact Finset.sum_insert hi

theorem weighted_flip_cancel (trace : AddressTrace k) (b : Fin k → Bool) (i : Fin k)
    (hi : i ∉ knownCoordinates trace) (F : (Fin k → Bool) → ℝ)
    (hF : ∀ a, F (flipAddress i a) = F a) :
    (∑ a, sliceWeight trace a * agreement a b i * F a) = 0 := by
  have he := (flipEquiv i).sum_comp (fun a => sliceWeight trace a * agreement a b i * F a)
  change (∑ a, sliceWeight trace (flipAddress i a) * agreement (flipAddress i a) b i *
    F (flipAddress i a)) = _ at he
  simp_rw [sliceWeight_flip trace i hi, agreement_flip, hF] at he
  have hn : (∑ a, sliceWeight trace a * -agreement a b i * F a) =
      -(∑ a, sliceWeight trace a * agreement a b i * F a) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hn] at he
  linarith

def moment (trace : AddressTrace k) (b : Fin k → Bool) (s : Finset (Fin k)) (p : ℕ) : ℝ :=
  ∑ a, sliceWeight trace a * signedSum b s a ^ p

theorem moment_two_insert (trace : AddressTrace k) (b : Fin k → Bool)
    (s : Finset (Fin k)) (i : Fin k) (hi : i ∉ s) (hknown : i ∉ knownCoordinates trace) :
    moment trace b (insert i s) 2 = moment trace b s 2 + mass (sliceWeight trace) := by
  have hcancel := weighted_flip_cancel trace b i hknown (signedSum b s)
    (signedSum_flip b s i hi)
  have he : moment trace b (insert i s) 2 =
      (∑ a, (sliceWeight trace a * signedSum b s a ^ 2 +
        2 * (sliceWeight trace a * agreement a b i * signedSum b s a) + sliceWeight trace a)) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [signedSum_insert b s i hi]
    calc
      _ = sliceWeight trace a * agreement a b i ^ 2 +
          2 * (sliceWeight trace a * agreement a b i * signedSum b s a) +
          sliceWeight trace a * signedSum b s a ^ 2 := by ring
      _ = _ := by rw [agreement_sq]; ring
  rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hcancel, mul_zero, add_zero]
  rfl

theorem moment_four_insert (trace : AddressTrace k) (b : Fin k → Bool)
    (s : Finset (Fin k)) (i : Fin k) (hi : i ∉ s) (hknown : i ∉ knownCoordinates trace) :
    moment trace b (insert i s) 4 =
      moment trace b s 4 + 6 * moment trace b s 2 + mass (sliceWeight trace) := by
  have hcancel1 := weighted_flip_cancel trace b i hknown (signedSum b s)
    (signedSum_flip b s i hi)
  have hcancel3 := weighted_flip_cancel trace b i hknown (fun a => signedSum b s a ^ 3)
    (fun a => by simp only [signedSum_flip b s i hi])
  have he : moment trace b (insert i s) 4 =
      (∑ a, (sliceWeight trace a * signedSum b s a ^ 4 +
        4 * (sliceWeight trace a * agreement a b i * signedSum b s a ^ 3) +
        6 * (sliceWeight trace a * signedSum b s a ^ 2) +
        4 * (sliceWeight trace a * agreement a b i * signedSum b s a) + sliceWeight trace a)) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [signedSum_insert b s i hi]
    have h2 := agreement_sq a b i
    have h3 := agreement_cube a b i
    have h4 := agreement_fourth a b i
    calc
      _ = sliceWeight trace a * (agreement a b i ^ 4 +
          4 * agreement a b i ^ 3 * signedSum b s a +
          6 * agreement a b i ^ 2 * signedSum b s a ^ 2 +
          4 * agreement a b i * signedSum b s a ^ 3 + signedSum b s a ^ 4) := by ring
      _ = _ := by rw [h2, h3, h4]; ring
  rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hcancel1, hcancel3, mul_zero, add_zero]
  rfl

theorem moment_two_eq (trace : AddressTrace k) (b : Fin k → Bool) (s : Finset (Fin k))
    (hknown : ∀ i ∈ s, i ∉ knownCoordinates trace) :
    moment trace b s 2 = (s.card : ℝ) * mass (sliceWeight trace) := by
  induction s using Finset.induction_on with
  | empty => simp [moment, signedSum]
  | @insert i s hi ih =>
    have hki := hknown i (Finset.mem_insert_self i s)
    have hks : ∀ j ∈ s, j ∉ knownCoordinates trace :=
      fun j hj => hknown j (Finset.mem_insert_of_mem hj)
    rw [moment_two_insert trace b s i hi hki, ih hks, Finset.card_insert_of_notMem hi]
    push_cast
    ring

theorem moment_four_eq (trace : AddressTrace k) (b : Fin k → Bool) (s : Finset (Fin k))
    (hknown : ∀ i ∈ s, i ∉ knownCoordinates trace) :
    moment trace b s 4 = (3 * (s.card : ℝ) ^ 2 - 2 * (s.card : ℝ)) *
      mass (sliceWeight trace) := by
  induction s using Finset.induction_on with
  | empty => simp [moment, signedSum]
  | @insert i s hi ih =>
    have hki := hknown i (Finset.mem_insert_self i s)
    have hks : ∀ j ∈ s, j ∉ knownCoordinates trace :=
      fun j hj => hknown j (Finset.mem_insert_of_mem hj)
    rw [moment_four_insert trace b s i hi hki, ih hks,
      moment_two_eq trace b s hks, Finset.card_insert_of_notMem hi]
    push_cast
    ring

theorem moment_four_le (trace : AddressTrace k) (b : Fin k → Bool) (s : Finset (Fin k))
    (hknown : ∀ i ∈ s, i ∉ knownCoordinates trace) :
    moment trace b s 4 ≤ 3 * (k : ℝ) ^ 2 * mass (sliceWeight trace) := by
  rw [moment_four_eq trace b s hknown]
  apply mul_le_mul_of_nonneg_right _ (mass_nonnegative (sliceWeight_nonnegative trace))
  have hc0 : 0 ≤ (s.card : ℝ) := Nat.cast_nonneg _
  have hck : (s.card : ℝ) ≤ k := by
    exact_mod_cast (show s.card ≤ k by simpa using Finset.card_le_univ s)
  nlinarith

theorem signedSum_le_card (b : Fin k → Bool) (s : Finset (Fin k)) (a : Fin k → Bool) :
    signedSum b s a ≤ (s.card : ℝ) := by
  calc
    _ ≤ ∑ _i ∈ s, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
      simp only [agreement]
      split_ifs <;> norm_num
    _ = _ := by simp

theorem signedSum_univ (a b : Fin k → Bool) :
    signedSum b Finset.univ a = (k : ℝ) - 2 * (distance a b : ℝ) := by
  have he (i : Fin k) : agreement a b i =
      1 - 2 * (if a i ≠ b i then (1 : ℝ) else 0) := by
    by_cases h : a i = b i <;> norm_num [agreement, h]
  have hcount : (∑ i, if a i ≠ b i then (1 : ℝ) else 0) = (distance a b : ℝ) := by
    rw [Finset.sum_boole]
    rfl
  simp only [signedSum, he, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hcount]
  simp

theorem signedSum_unknown_lower (radius budget : ℕ) (trace : AddressTrace k)
    (htrace : trace.length ≤ budget) (a b : Fin k → Bool) (hin : distance a b ≤ radius) :
    (k : ℝ) - 2 * (radius : ℝ) - (budget : ℝ) ≤
      signedSum b (Finset.univ \ knownCoordinates trace) a := by
  have hsplit : signedSum b (Finset.univ \ knownCoordinates trace) a +
      signedSum b (knownCoordinates trace) a = signedSum b Finset.univ a :=
    Finset.sum_sdiff (Finset.subset_univ _)
  rw [signedSum_univ] at hsplit
  have hs := signedSum_le_card b (knownCoordinates trace) a
  have hc : ((knownCoordinates trace).card : ℝ) ≤ trace.length := by
    exact_mod_cast knownCoordinates_card_le trace
  have ht : (trace.length : ℝ) ≤ budget := by exact_mod_cast htrace
  have hd : (distance a b : ℝ) ≤ radius := by exact_mod_cast hin
  linarith

/-- A fourth-moment estimate for every address subcube, including traces with
repeated coordinates. No concentration inequality is imported or assumed. -/
theorem ballMass_fourth_moment (radius budget : ℕ) (trace : AddressTrace k)
    (htrace : trace.length ≤ budget) (b : Fin k → Bool)
    (hgap : 0 < (k : ℝ) - 2 * (radius : ℝ) - (budget : ℝ)) :
    ballMass radius trace b ≤
      (3 * (k : ℝ) ^ 2 / ((k : ℝ) - 2 * (radius : ℝ) - (budget : ℝ)) ^ 4) *
        mass (sliceWeight trace) := by
  let gap : ℝ := (k : ℝ) - 2 * (radius : ℝ) - (budget : ℝ)
  let unknown := Finset.univ \ knownCoordinates trace
  have hgap' : 0 < gap := hgap
  have hknown : ∀ i ∈ unknown, i ∉ knownCoordinates trace :=
    fun i hi => (Finset.mem_sdiff.mp hi).2
  have hm := moment_four_le trace b unknown hknown
  have hmarkov : gap ^ 4 * ballMass radius trace b ≤ moment trace b unknown 4 := by
    simp only [ballMass, moment, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    by_cases hin : distance a b ≤ radius
    · simp only [hin, if_true]
      have hs : gap ≤ signedSum b unknown a :=
        signedSum_unknown_lower radius budget trace htrace a b hin
      have hp := pow_le_pow_left₀ (le_of_lt hgap') hs 4
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left hp (sliceWeight_nonnegative trace a)
    · simp only [hin, if_false, mul_zero]
      exact mul_nonneg (sliceWeight_nonnegative trace a) (by positivity)
  have hg4 : 0 < gap ^ 4 := pow_pos hgap' _
  have h := hmarkov.trans hm
  calc
    ballMass radius trace b ≤ (3 * (k : ℝ) ^ 2 * mass (sliceWeight trace)) / gap ^ 4 :=
      (le_div_iff₀ hg4).2 (by simpa only [mul_comm] using h)
    _ = _ := by dsimp [gap]; ring

theorem ballSliceBound_fourth_moment (radius budget : ℕ)
    (hgap : 0 < (k : ℝ) - 2 * (radius : ℝ) - (budget : ℝ)) :
    @BallSliceBound k radius budget
      (3 * (k : ℝ) ^ 2 / ((k : ℝ) - 2 * (radius : ℝ) - (budget : ℝ)) ^ 4) :=
  fun trace htrace b => ballMass_fourth_moment radius budget trace htrace b hgap

end QueryComplexity.ApproxIndex
