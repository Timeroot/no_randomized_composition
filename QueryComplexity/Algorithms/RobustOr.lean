import QueryComplexity.Randomized.StoppingTime

/-! A fixed-cap robust OR evaluator. Each coin is tested by a walk started at
height `a`; a walk advances to the next coin only on hitting zero. Finishing
all walks rejects, and reaching the global cap accepts. No upper boundary
or accuracy amplification for individual coins is needed. -/

namespace QueryComplexity.RobustOr

inductive State where
  | reject
  | testing (index score : ℕ)

def Invariant (m : ℕ) : State → Prop
  | .reject => True
  | .testing index score => index < m ∧ 0 < score

def next (m a index score : ℕ) (answer : Bool) : State :=
  if answer then .testing index (score + 1)
  else if score ≤ 1 then
    if index + 1 < m then .testing (index + 1) a else .reject
  else .testing index (score - 1)

def step (m a : ℕ) : State → QueryStep (Fin m) Bool State Bool
  | .reject => .done false
  | .testing index score =>
      if hi : index < m then .ask ⟨index, hi⟩ (next m a index score) else .done false

theorem invariant_next {m a index score : ℕ} (ha : 0 < a)
    (hstate : Invariant m (.testing index score)) (answer : Bool) :
    Invariant m (next m a index score answer) := by
  cases answer <;> grind [Invariant, next]

noncomputable def durationPotential (m a : ℕ) : State → ℝ
  | .reject => 0
  | .testing index score => 3 * ((a : ℝ) * ((m - index - 1 : ℕ) : ℝ) + score)

theorem durationPotential_nonneg (m a : ℕ) (state : State) :
    0 ≤ durationPotential m a state := by
  cases state <;> simp only [durationPotential] <;> positivity

theorem durationPotential_ge_one {m a index score : ℕ}
    (hstate : Invariant m (.testing index score)) :
    1 ≤ durationPotential m a (.testing index score) := by
  have hs : (1 : ℝ) ≤ score := by exact_mod_cast hstate.2
  have hterm : 0 ≤ (a : ℝ) * ((m - index - 1 : ℕ) : ℝ) := by positivity
  simp only [durationPotential]
  nlinarith

theorem durationPotential_up (m a index score : ℕ) :
    durationPotential m a (next m a index score true) =
      durationPotential m a (.testing index score) + 3 := by
  simp [next, durationPotential]
  ring

theorem durationPotential_down {m a index score : ℕ}
    (hstate : Invariant m (.testing index score)) :
    durationPotential m a (next m a index score false) =
      durationPotential m a (.testing index score) - 3 := by
  rcases hstate with ⟨hi, hs⟩
  simp only [next, Bool.false_eq_true, ↓reduceIte]
  by_cases hscore : score ≤ 1
  · have hscore' : score = 1 := by omega
    rw [if_pos hscore]
    by_cases hindex : index + 1 < m
    · rw [if_pos hindex]
      have hrem : ((m - (index + 1) - 1 : ℕ) : ℝ) + 1 = ((m - index - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : (m - (index + 1) - 1) + 1 = m - index - 1)
      simp only [durationPotential, hscore', Nat.cast_one]
      rw [← hrem]
      ring
    · rw [if_neg hindex]
      have hrem : m - index - 1 = 0 := by omega
      simp [durationPotential, hscore', hrem]
  · rw [if_neg hscore]
    have hsreal : ((score - 1 : ℕ) : ℝ) + 1 = (score : ℝ) := by
      exact_mod_cast (by omega : score - 1 + 1 = score)
    simp only [durationPotential]
    rw [← hsreal]
    ring

theorem durationPotential_drift {m a index score : ℕ}
    (hstate : Invariant m (.testing index score)) (p : ℝ) (hp : p ≤ 1 / 3) :
    (1 - p) * durationPotential m a (next m a index score false) +
      p * durationPotential m a (next m a index score true) ≤
        durationPotential m a (.testing index score) - 1 := by
  rw [durationPotential_down hstate, durationPotential_up]
  nlinarith

theorem durationPotential_initial {m a : ℕ} (hm : 0 < m) :
    durationPotential m a (.testing 0 a) = 3 * a * m := by
  have hrem : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
    exact_mod_cast (by omega : m - 1 + 1 = m)
  simp only [durationPotential, Nat.sub_zero]
  rw [← hrem]
  ring

/-- If every coin favors false by at least `2/3`, the capped evaluator has
false-positive probability bounded by its initial duration potential. -/
theorem false_positive_bound {m a : ℕ} (ha : 0 < a)
    (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hzero : ∀ i, p i ≤ 1 / 3)
    (n : ℕ) (state : State) (hstate : Invariant m state) :
    RandomizedOracle.value p (step m a) (fun b => if b then 1 else 0) true (n + 1) state ≤
      durationPotential m a state / ((n : ℝ) + 1) := by
  have h := RandomizedOracle.accept_with_cap_le p hp (step m a) (Invariant m)
    (fun _ => 0) (durationPotential m a)
    (fun state _ => ⟨le_rfl, durationPotential_nonneg m a state⟩) ?_ n state hstate
  · simpa using h
  · intro state hstate
    cases state with
    | reject => simp [step]
    | testing index score =>
        have hi := hstate.1
        simp only [step, dif_pos hi]
        exact ⟨invariant_next ha hstate false, invariant_next ha hstate true,
          durationPotential_ge_one hstate, by simp,
          durationPotential_drift hstate (p ⟨index, hi⟩) (hzero _)⟩

noncomputable def reciprocalScore (score : ℕ) : ℝ := 1 / (2 : ℝ) ^ score

theorem reciprocalScore_nonneg (score : ℕ) : 0 ≤ reciprocalScore score := by
  unfold reciprocalScore
  positivity

theorem reciprocalScore_up (score : ℕ) : reciprocalScore (score + 1) = reciprocalScore score / 2 := by
  simp [reciprocalScore, pow_succ, div_eq_mul_inv, mul_inv_rev]
  ring

theorem reciprocalScore_down {score : ℕ} (hs : 0 < score) :
    reciprocalScore (score - 1) = 2 * reciprocalScore score := by
  have h := reciprocalScore_up (score - 1)
  rw [Nat.sub_add_cancel hs] at h
  linarith

/-- A false-output potential centered at one designated positive coin. -/
noncomputable def goodRisk {m : ℕ} (a : ℕ) (good : Fin m) : State → ℝ
  | .reject => 1
  | .testing index score =>
      if index < good.val then reciprocalScore a
      else if index = good.val then reciprocalScore score else 1

theorem goodRisk_nonneg {m : ℕ} (a : ℕ) (good : Fin m) (state : State) :
    0 ≤ goodRisk a good state := by
  cases state with
  | reject => exact zero_le_one
  | testing index score =>
      simp only [goodRisk]
      split_ifs <;> first | exact reciprocalScore_nonneg _ | exact zero_le_one

theorem goodRisk_before_next {m a index score : ℕ} (good : Fin m)
    (hbefore : index < good.val) (answer : Bool) :
    goodRisk a good (next m a index score answer) = reciprocalScore a := by
  cases answer <;> grind [next, goodRisk]

theorem goodRisk_after_next {m a index score : ℕ} (good : Fin m)
    (hafter : good.val < index) (answer : Bool) :
    goodRisk a good (next m a index score answer) = 1 := by
  cases answer <;> grind [next, goodRisk]

theorem goodRisk_at_up {m a score : ℕ} (good : Fin m) :
    goodRisk a good (next m a good.val score true) = reciprocalScore score / 2 := by
  simp [next, goodRisk, reciprocalScore_up]

theorem goodRisk_at_down {m a score : ℕ} (good : Fin m) (hs : 0 < score) :
    goodRisk a good (next m a good.val score false) = 2 * reciprocalScore score := by
  simp only [next, Bool.false_eq_true, ↓reduceIte]
  by_cases hscore : score ≤ 1
  · have heq : score = 1 := by omega
    rw [if_pos hscore]
    by_cases hindex : good.val + 1 < m
    · rw [if_pos hindex]
      simp [goodRisk, heq, reciprocalScore]
    · simp [hindex, goodRisk, heq, reciprocalScore]
  · rw [if_neg hscore]
    simpa [goodRisk] using reciprocalScore_down hs

theorem goodRisk_drift {m a index score : ℕ} (good : Fin m)
    (hs : 0 < score) (p : ℝ) (hgood : index = good.val → 2 / 3 ≤ p) :
    (1 - p) * goodRisk a good (next m a index score false) +
      p * goodRisk a good (next m a index score true) ≤ goodRisk a good (.testing index score) := by
  rcases lt_trichotomy index good.val with hbefore | heq | hafter
  · rw [goodRisk_before_next good hbefore false, goodRisk_before_next good hbefore true]
    simp only [goodRisk, if_pos hbefore]
    nlinarith
  · subst index
    rw [goodRisk_at_down good hs, goodRisk_at_up good]
    simp only [goodRisk, lt_self_iff_false, if_false, if_true]
    have hmul := mul_nonneg (reciprocalScore_nonneg score) (sub_nonneg.mpr (hgood rfl))
    nlinarith
  · rw [goodRisk_after_next good hafter false, goodRisk_after_next good hafter true]
    simp only [goodRisk, if_neg (show ¬ index < good.val by omega),
      if_neg (show index ≠ good.val by omega)]
    nlinarith

theorem goodRisk_initial {m : ℕ} (a : ℕ) (good : Fin m) :
    goodRisk a good (.testing 0 a) = reciprocalScore a := by
  by_cases hz : good.val = 0
  · simp [goodRisk, hz]
  · have hpos : 0 < good.val := by omega
    simp [goodRisk, hpos]

/-- A positive designated coin limits rejection, regardless of all other biases. -/
theorem false_negative_bound {m a : ℕ} (ha : 0 < a)
    (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (good : Fin m) (hgood : 2 / 3 ≤ p good) (n : ℕ) (state : State)
    (hstate : Invariant m state) :
    RandomizedOracle.value p (step m a) (fun b => if b then 0 else 1) true n state ≤
      goodRisk a good state := by
  apply RandomizedOracle.value_le_potential p hp (step m a) _ true (Invariant m) (goodRisk a good)
    (fun state _ => goodRisk_nonneg a good state) ?_ n state hstate
  intro state hstate
  cases state with
  | reject => simp [step, goodRisk]
  | testing index score =>
      have hi := hstate.1
      simp only [step, dif_pos hi]
      refine ⟨invariant_next ha hstate false, invariant_next ha hstate true, ?_⟩
      apply goodRisk_drift good hstate.2 (p ⟨index, hi⟩)
      intro heq
      have hquery : (⟨index, hi⟩ : Fin m) = good := Fin.ext heq
      simpa only [hquery] using hgood

variable {Seed T : Type*} [Fintype Seed] {m : ℕ}

/-- The actual randomized binary query algorithm with the specified global cap. -/
noncomputable def algorithm (oracle : RandomizedOracle Seed (Fin m) T) (a cap : ℕ) :
    FiniteRandomizedTree (RandomizedOracle.Seeds Seed (cap + 1)) T Bool :=
  oracle.algorithm (step m a) true (cap + 1) (.testing 0 a)

theorem algorithm_depthBound (oracle : RandomizedOracle Seed (Fin m) T) (a cap : ℕ)
    {cost : ℕ} (hcost : ∀ query seed, (oracle.tree query seed).depth ≤ cost) :
    (algorithm oracle a cap).DepthBound ((cap + 1) * cost) :=
  oracle.algorithm_depthBound _ _ hcost _ _

theorem algorithm_accept_le (oracle : RandomizedOracle Seed (Fin m) T)
    (a cap : ℕ) (ha : 0 < a) (hm : 0 < m) (x : T → Bool)
    (hzero : ∀ i, oracle.acceptProbability x i ≤ 1 / 3) :
    (algorithm oracle a cap).probability (fun b => b = true) x ≤
      (3 * (a : ℝ) * m) / ((cap : ℝ) + 1) := by
  unfold algorithm
  rw [FiniteRandomizedTree.probability_eq_expectation, RandomizedOracle.expectation_algorithm]
  have h := false_positive_bound ha (oracle.acceptProbability x) (oracle.acceptProbability_bounds x)
    hzero cap (.testing 0 a) ⟨hm, ha⟩
  simpa only [durationPotential_initial hm] using h

theorem algorithm_reject_le (oracle : RandomizedOracle Seed (Fin m) T)
    (a cap : ℕ) (ha : 0 < a) (hm : 0 < m) (x : T → Bool)
    (good : Fin m) (hgood : 2 / 3 ≤ oracle.acceptProbability x good) :
    (algorithm oracle a cap).probability (fun b => b = false) x ≤ reciprocalScore a := by
  unfold algorithm
  rw [FiniteRandomizedTree.probability_eq_expectation, RandomizedOracle.expectation_algorithm]
  have heq : (fun b : Bool => if b = false then (1 : ℝ) else 0) =
      fun b => if b then 0 else 1 := by funext b; cases b <;> simp
  rw [heq]
  have h := false_negative_bound ha (oracle.acceptProbability x) (oracle.acceptProbability_bounds x)
    good hgood (cap + 1) (.testing 0 a) ⟨hm, ha⟩
  simpa only [goodRisk_initial] using h

/-- A constant-error robust OR with a fixed linear cap. -/
noncomputable def robust (oracle : RandomizedOracle Seed (Fin m) T) :
    FiniteRandomizedTree (RandomizedOracle.Seeds Seed (3000 * m + 1)) T Bool :=
  algorithm oracle 10 (3000 * m)

theorem robust_depthBound (oracle : RandomizedOracle Seed (Fin m) T) (hm : 0 < m)
    {cost : ℕ} (hcost : ∀ query seed, (oracle.tree query seed).depth ≤ cost) :
    (robust oracle).DepthBound (3001 * m * cost) := by
  have h := algorithm_depthBound oracle 10 (3000 * m) hcost
  intro seed
  exact (h seed).trans (Nat.mul_le_mul_right cost (by omega))

/-- If all component algorithms accept with probability at most `1/3`,
the robust OR accepts with probability at most `1/100`. -/
theorem robust_zero (oracle : RandomizedOracle Seed (Fin m) T) (hm : 0 < m) (x : T → Bool)
    (hzero : ∀ i, oracle.acceptProbability x i ≤ 1 / 3) :
    (robust oracle).probability (fun b => b = true) x ≤ 1 / 100 := by
  calc
    _ ≤ (3 * (10 : ℝ) * m) / (((3000 * m : ℕ) : ℝ) + 1) :=
      algorithm_accept_le oracle 10 (3000 * m) (by norm_num) hm x hzero
    _ ≤ 1 / 100 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((3000 * m : ℕ) : ℝ) + 1)).2
      push_cast
      nlinarith

/-- One component accepting with probability at least `2/3` suffices, even
when every other component has an arbitrary acceptance probability. -/
theorem robust_one (oracle : RandomizedOracle Seed (Fin m) T) (hm : 0 < m) (x : T → Bool)
    (good : Fin m) (hgood : 2 / 3 ≤ oracle.acceptProbability x good) :
    (robust oracle).probability (fun b => b = false) x ≤ 1 / 100 := by
  calc
    _ ≤ reciprocalScore 10 := algorithm_reject_le oracle 10 (3000 * m) (by norm_num) hm x good hgood
    _ ≤ 1 / 100 := by norm_num [reciprocalScore]

end QueryComplexity.RobustOr
