import QueryComplexity.Pointer

namespace QueryComplexity.Pointer

theorem rho_discrete_eq (q : ℕ) (hq : Odd q) :
    (((q - 1) / 2 : ℕ) : ℝ) / (q : ℝ) = ((q : ℝ) - 1) / (2 * q) := by
  obtain ⟨r, hr⟩ := hq
  have hdiv : (q - 1) / 2 = r := by omega
  rw [hdiv, hr]
  push_cast
  field_simp
  ring

/-- Convert the exact detector's balanced acceptance probability to uniform
success bias for odd majority. -/
theorem balanced_success (q t : ℕ) (hq : 3 ≤ q) (hodd : Odd q) :
    let rho := ((q : ℝ) - 1) / (2 * q)
    let alpha := (1 - rho) / (2 - rho)
    let p := alpha + (1 - alpha) * (rho * t / q)
    (if q < 2 * t then p else 1 - p) ≥ (1 : ℝ) / 2 + 1 / (10 * q) := by
  dsimp
  set rho : ℝ := ((q : ℝ) - 1) / (2 * q)
  set p : ℝ := (1 - rho) / (2 - rho) +
    (1 - (1 - rho) / (2 - rho)) * (rho * t / q)
  have hqreal : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by positivity
  have hr := detector_rho_bounds (q : ℝ) hqreal
  have hd : 0 < (2 - rho) * q := mul_pos (by dsimp [rho]; linarith [hr.2]) hqpos
  have hid : 2 * p - 1 = (rho / ((2 - rho) * q)) * (2 * t - q) := by
    have h := balanced_acceptance_identity (q : ℝ) rho (t : ℝ) (ne_of_gt hqpos)
      (by dsimp [rho]; linarith [hr.2])
    dsimp at h
    change 2 * p - 1 = _ at h
    rw [h]
    ring
  have hb := weak_bias_scale (q : ℝ) hqreal
  change 1 / (5 * (q : ℝ)) ≤ rho / ((2 - rho) * q) at hb
  have hk : 0 ≤ rho / ((2 - rho) * q) := (by positivity : 0 ≤ 1 / (5 * (q : ℝ))).trans hb
  have hhalf : 2 * (1 / (10 * (q : ℝ))) = 1 / (5 * (q : ℝ)) := by ring
  split_ifs with hmajor
  · have hgap : (1 : ℝ) ≤ 2 * t - q := by
      have hn : (q : ℝ) + 1 ≤ 2 * (t : ℝ) := by exact_mod_cast (by omega : q + 1 ≤ 2 * t)
      linarith
    have hm := mul_le_mul_of_nonneg_left hgap hk
    nlinarith
  · have hgapnat : 2 * t + 1 ≤ q := by
      obtain ⟨r, hr⟩ := hodd
      omega
    have hgap : (2 : ℝ) * t - q ≤ -1 := by
      have hn : (2 : ℝ) * t + 1 ≤ q := by exact_mod_cast hgapnat
      linarith
    have hm := mul_le_mul_of_nonneg_left hgap hk
    nlinarith

end QueryComplexity.Pointer
