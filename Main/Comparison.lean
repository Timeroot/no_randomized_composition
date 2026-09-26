import Main.OuterLowerBound
import Mathlib.Analysis.SpecificLimits.Basic
import Main.UpperBound
import Main.Statement
import Mathlib.Analysis.Asymptotics.Lemmas

/-! The asymptotic comparison. Bounds on the sparse parameter sequence
combine the outer lower bound and the composition upper bound; the final
criterion takes the independently proved inner lower bound. -/

open Filter Asymptotics
open scoped Topology

namespace QueryComplexity.Construction

/-- A vanishing multiplicative upper bound implies little-o. -/
private theorem littleO_of_eventual_rate {u v e : ℕ → ℝ}
    (he : IsLittleO atTop e (fun _ => (1 : ℝ)))
    (hu : ∀ᶠ n in atTop, ‖u n‖ ≤ e n * ‖v n‖) :
    IsLittleO atTop u v := by
  apply IsLittleO.of_bound
  intro c hc
  filter_upwards [he.bound hc, hu] with n hen hun
  have hen' : e n ≤ c := (le_abs_self _).trans (by simpa using hen)
  grw [hun, hen']

private theorem sparse_rate_bound (n : ℕ) :
    (3 : ℝ) ^ n / scale n ≤ ((3 : ℝ) / 4) ^ n / 10 := by
  have hpow : (4 : ℝ) ^ n ≤ (2 : ℝ) ^ (2 ^ n) := by
    calc
      _ = (2 : ℝ) ^ (2 * n) := by rw [pow_mul]; norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (Nat.mul_le_pow (by omega : 2 ≠ 1) n)
  rw [scale_cast]
  calc
    _ ≤ (3 : ℝ) ^ n / (10 * 4 ^ n) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
    _ = _ := by rw [div_pow]; ring

private theorem sparse_rate_tendsto :
    Tendsto (fun n : ℕ => (3 : ℝ) ^ n / scale n) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => by positivity) sparse_rate_bound
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 : ℝ) / 4 < 1)).div_const 10
  simpa using h

theorem amplification_rate_littleO (C : ℝ) (offset : ℕ) :
    IsLittleO atTop (fun n : ℕ => C * (3 : ℝ) ^ (n + offset) / scale n)
      (fun _ => (1 : ℝ)) := by
  apply (isLittleO_one_iff ℝ).mpr
  have h := sparse_rate_tendsto.const_mul (C * (3 : ℝ) ^ offset)
  convert h using 1
  · funext n
    rw [pow_add]
    ring
  · simp

/-- Four extra amplification stages cover all `100 * scale n` core copies. -/
theorem copies_amplification_error (n : ℕ) :
    (copies n : ℝ) * ((1 : ℝ) / 3 * (1 / 2) ^ (2 ^ (n + 4))) ≤ 1 / 6 := by
  have hpow : 2 ^ (n + 4) = 2 ^ n + 15 * 2 ^ n := by rw [pow_add]; ring
  have hsmall : (1 / 2 : ℝ) ^ (15 * 2 ^ n) ≤ (1 / 2 : ℝ) ^ 15 := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    have h : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by omega)
    omega
  have hc : (copies n : ℝ) = 1000 * (2 : ℝ) ^ (2 ^ n) := by
    simp only [copies, Nat.cast_mul, Nat.cast_ofNat, scale_cast]
    ring
  rw [hc, hpow, pow_add]
  have hcancel : (2 : ℝ) ^ (2 ^ n) * (1 / 2) ^ (2 ^ n) = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = (1000 : ℝ) / 3 * ((2 : ℝ) ^ (2 ^ n) * (1 / 2) ^ (2 ^ n)) *
        (1 / 2) ^ (15 * 2 ^ n) := by ring
    _ = (1000 : ℝ) / 3 * (1 / 2) ^ (15 * 2 ^ n) := by rw [hcancel, mul_one]
    _ ≤ (1000 : ℝ) / 3 * (1 / 2) ^ 15 := by gcongr
    _ ≤ _ := by norm_num

/-- Algebraic cancellation of the common seed and encoding factors. -/
private theorem composition_coefficient_bound (C ell t m q a RF RG RC : ℝ)
    (hC : 0 ≤ C) (hell : 0 < ell) (ht : 0 ≤ t)
    (hq : 0 ≤ q) (ha : 0 ≤ a)
    (hF : 25 * ell * m ^ 2 * q ^ 3 ≤ RF)
    (hG : a * q ^ 2 * ell / 1000000 ≤ RG)
    (hupper : RC ≤ C * ell * t * m ^ 2 * q ^ 5 * a) :
    RC ≤ (40000 * C * t / ell) * (RF * RG) := by
  have hRF : 0 ≤ RF := (show 0 ≤ 25 * ell * m ^ 2 * q ^ 3 by positivity).trans hF
  calc
    RC ≤ C * ell * t * m ^ 2 * q ^ 5 * a := hupper
    _ = (40000 * C * t / ell) *
        ((25 * ell * m ^ 2 * q ^ 3) * (a * q ^ 2 * ell / 1000000)) := by
      field_simp
      ring
    _ ≤ _ := by grw [hF, hG]

/-- A deliberately loose fixed constant absorbs the concrete algorithm's
amplification, robust formula evaluation, and exact certificate verification. -/
private theorem raw_composition_cost_bound (q m ell t a : ℕ)
    (hq : 1 ≤ q) (hm : 1 ≤ m) (hell : 1 ≤ ell) :
    (100 * ell) * 27 * 3 ^ t * 3001 ^ 2 * m ^ 2 *
        (10000 * q ^ 4 * (6 * q + 2) * (36 * a) + q ^ 3 * (36 * a)) +
      (36 * (1 + (100 * ell) * (m ^ 2 + 1)) + (100 * ell) * m ^ 2) *
        (q ^ 3 * (36 * a)) ≤
      10 ^ 18 * ell * 3 ^ t * m ^ 2 * q ^ 5 * a := by
  have hq3 : q ^ 3 ≤ q ^ 5 := Nat.pow_le_pow_right hq (by omega)
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm
  have ht : 1 ≤ 3 ^ t := Nat.one_le_pow _ _ (by omega)
  have hseed : 10000 * q ^ 4 * (6 * q + 2) * (36 * a) + q ^ 3 * (36 * a) ≤
      (80001 * 36) * q ^ 5 * a := by
    calc
      _ ≤ 10000 * q ^ 4 * (8 * q) * (36 * a) + q ^ 5 * (36 * a) := by
        gcongr
        omega
      _ = _ := by ring
  have hv : 36 * (1 + (100 * ell) * (m ^ 2 + 1)) + (100 * ell) * m ^ 2 ≤
      109 * (100 * ell) * m ^ 2 := by
    have hcm : 1 ≤ (100 * ell) * m ^ 2 := by nlinarith
    have hcm2 : 100 * ell ≤ (100 * ell) * m ^ 2 := by nlinarith
    nlinarith
  calc
    _ ≤ (100 * ell) * 27 * 3 ^ t * 3001 ^ 2 * m ^ 2 * ((80001 * 36) * q ^ 5 * a) +
        (109 * (100 * ell) * m ^ 2) * (q ^ 5 * (36 * a)) := by gcongr
    _ ≤ (100 * ell) * 27 * 3 ^ t * 3001 ^ 2 * m ^ 2 * ((80001 * 36) * q ^ 5 * a) +
        (109 * (100 * ell) * m ^ 2) * (q ^ 5 * (36 * a)) * 3 ^ t := by
      have hh := Nat.mul_le_mul_left ((109 * (100 * ell) * m ^ 2) * (q ^ 5 * (36 * a))) ht
      exact Nat.add_le_add_left (by simpa only [Nat.mul_one] using hh) _
    _ = (100 * 27 * 3001 ^ 2 * 80001 * 36 + 109 * 100 * 36) *
        (ell * 3 ^ t * m ^ 2 * q ^ 5 * a) := by ring
    _ ≤ _ := by
      have hnum : 100 * 27 * 3001 ^ 2 * 80001 * 36 + 109 * 100 * 36 ≤ (10 : ℕ) ^ 18 := by norm_num
      calc
        _ ≤ 10 ^ 18 * (ell * 3 ^ t * m ^ 2 * q ^ 5 * a) :=
          Nat.mul_le_mul_right (ell * 3 ^ t * m ^ 2 * q ^ 5 * a) hnum
        _ = _ := by ring

end QueryComplexity.Construction

open Filter Asymptotics

namespace QueryComplexity.Construction

theorem totalComposedCost_le (n : ℕ) :
    totalComposedCost (pointerArity n) (copies n) (n + 4) ≤
      10 ^ 18 * scale n * 3 ^ (n + 4) * seedLength (pointerArity n) ^ 2 *
        pointerArity n ^ 5 * pointerPayloadWidth (pointerArity n) := by
  have h := raw_composition_cost_bound (pointerArity n) (seedLength (pointerArity n))
    (scale n) (n + 4) (pointerPayloadWidth (pointerArity n))
    ((by omega : 1 ≤ 3).trans (pointerArity_ge_three n)) (seedLength_pos _)
    ((by omega : 1 ≤ 10).trans (scale_ge_ten n))
  convert h using 1
  simp only [totalComposedCost, composedCoreCost, composedSeedCost, outerVerifierCost,
    cellWidth, copies, payloadWidth, ApproxIndex.seedSize]
  ring

/-- The composed functions' upper bound, with all algorithms and error bounds
instantiated and no complexity assumptions. -/
theorem R_composition_upper (n : ℕ) :
    R (comp (F n) (G n)) ≤
      10 ^ 18 * scale n * 3 ^ (n + 4) * seedLength (pointerArity n) ^ 2 *
        pointerArity n ^ 5 * pointerPayloadWidth (pointerArity n) := by
  rw [F, G, R_comp_toFin]
  exact (R_comp_le_totalComposedCost (pointerArity n) (copies n)
    (pointerArity_ge_three n) (pointerArity_odd n) (n + 4)
    ((copies_amplification_error n).trans (by norm_num))).trans (totalComposedCost_le n)

/-- Only the inner lower bound remains as a premise in this quantitative
comparison; the outer lower and composed upper are proved for the actual family. -/
theorem composition_rate_of_inner_lower (n : ℕ)
    (hG : (pointerPayloadWidth (pointerArity n) : ℝ) * (pointerArity n : ℝ) ^ 2 *
      (scale n : ℝ) / 1000000 ≤ (R (G n) : ℝ)) :
    (R (comp (F n) (G n)) : ℝ) ≤
      (40000 * (10 : ℝ) ^ 18 * 3 ^ (n + 4) / scale n) *
        ((R (F n) : ℝ) * (R (G n) : ℝ)) := by
  have hF : 25 * (scale n : ℝ) * (seedLength (pointerArity n) : ℝ) ^ 2 *
      (pointerArity n : ℝ) ^ 3 ≤ (R (F n) : ℝ) := by
    have h := R_F_lower n
    exact_mod_cast (by simpa only [pow_two, Nat.mul_assoc] using h)
  have hupper : (R (comp (F n) (G n)) : ℝ) ≤
      10 ^ 18 * (scale n : ℝ) * 3 ^ (n + 4) * (seedLength (pointerArity n) : ℝ) ^ 2 *
        (pointerArity n : ℝ) ^ 5 * (pointerPayloadWidth (pointerArity n) : ℝ) := by
    exact_mod_cast R_composition_upper n
  exact composition_coefficient_bound _ _ _ _ _ _ _ _ _ (by positivity)
    (by exact_mod_cast (show 0 < scale n by have := scale_ge_ten n; omega))
    (by positivity) (by positivity) (by positivity) hF hG hupper

theorem counterexample_of_eventual_inner_lower
    (hG : ∀ᶠ n in atTop,
      (pointerPayloadWidth (pointerArity n) : ℝ) * (pointerArity n : ℝ) ^ 2 *
        (scale n : ℝ) / 1000000 ≤ (R (G n) : ℝ)) : TotalCompositionCounterexample := by
  refine ⟨_, _, F, G, fun n => ⟨F_R_pos n, G_R_pos n⟩, ?_⟩
  apply littleO_of_eventual_rate (amplification_rate_littleO (40000 * (10 : ℝ) ^ 18) 4)
  filter_upwards [hG] with n hn
  simpa only [Real.norm_eq_abs, Nat.abs_cast, abs_mul] using
    composition_rate_of_inner_lower n hn

end QueryComplexity.Construction
