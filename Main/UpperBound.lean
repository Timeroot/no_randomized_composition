import QueryComplexity.Randomized.Amplification
import Main.Construction
import QueryComplexity.PointerFunction.Algorithms
import QueryComplexity.ApproxIndex.Composition
import QueryComplexity.Algorithms.RobustAndOr
import QueryComplexity.CheatSheet.Algorithm

namespace QueryComplexity.Construction

def cellWidth (q : ℕ) : ℕ := 36 * pointerPayloadWidth q

theorem card_innerCoordinates (q : ℕ) : Fintype.card (InnerCoordinates q) = q ^ 3 * cellWidth q := by
  simp only [InnerCoordinates, Fintype.card_prod, Fintype.card_fin, cellWidth]
  ring

def composedSeedCost (q : ℕ) : ℕ :=
  ApproxIndex.seedSize q * ((6 * q + 2) * cellWidth q) + q ^ 3 * cellWidth q

noncomputable def composedSeedAlgorithm (q : ℕ) (hq : 3 ≤ q) :=
  ApproxIndex.composedAlgorithm (k := ApproxIndex.seedSize q) (inner q)
    (Pointer.balancedWeakEvaluator (pointerDecoder q) hq)

theorem composedSeedAlgorithm_depthBound (q : ℕ) (hq : 3 ≤ q) :
    (composedSeedAlgorithm q hq).DepthBound (composedSeedCost q) := by
  have h := ApproxIndex.composedAlgorithm_depthBound (k := ApproxIndex.seedSize q) (inner q)
    (Pointer.balancedWeakEvaluator (pointerDecoder q) hq)
    (Pointer.balancedWeakEvaluator_depthBound (pointerDecoder q) hq)
  simpa only [composedSeedCost, Fintype.card_fin, cellWidth, card_innerCoordinates] using h

private theorem seed_radius_threshold (q : ℕ) (hq : 0 < q) :
    (ApproxIndex.seedSize q : ℝ) * (1 / 2 - 1 / (10 * q)) + 500 * (q : ℝ) ^ 3 =
      (ApproxIndex.seedRadius q : ℝ) := by
  unfold ApproxIndex.seedSize ApproxIndex.seedRadius
  rw [Nat.cast_sub (ApproxIndex.seedRadius_sub_le q)]
  push_cast
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  field_simp
  ring

theorem composedSeedAlgorithm_error (q : ℕ) (hq : 3 ≤ q) (hodd : Odd q)
    (x : ApproxIndexCoordinates (ApproxIndex.seedSize q) × InnerCoordinates q → Bool) (b : Bool)
    (hvalid : ApproxIndex.value (ApproxIndex.seedRadius q)
      (fun coordinate => inner q (fun u => x (coordinate, u))) = some b) :
    (composedSeedAlgorithm q hq).probability (fun output => output ≠ b) x ≤ 1 / 3 := by
  have hqpos : 0 < q := by omega
  have hqr : (0 : ℝ) < q := by exact_mod_cast hqpos
  have h := ApproxIndex.composedAlgorithm_error_le (inner q)
    (Pointer.balancedWeakEvaluator (pointerDecoder q) hq) (1 / (10 * q)) (500 * (q : ℝ) ^ 3)
    (by positivity)
    (Pointer.balancedWeakEvaluator_success (pointerDecoder q) hq hodd)
    (ApproxIndex.seedRadius q) (le_of_eq (seed_radius_threshold q hqpos)) x b
    ((ApproxIndex.value_eq_some_iff _ _ _).1 hvalid)
  refine h.trans ?_
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hdiv : (ApproxIndex.seedSize q : ℝ) / (4 * (500 * (q : ℝ) ^ 3) ^ 2) =
      1 / (100 * (q : ℝ) ^ 2) := by
    simp only [ApproxIndex.seedSize, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
    ring
  rw [hdiv]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 100 * (q : ℝ) ^ 2)).2
  nlinarith [sq_nonneg ((q : ℝ) - 1)]

noncomputable def composedCoreAlgorithm (q : ℕ) (hq : 3 ≤ q) :=
  KleeneAlgorithms.algorithm (m := seedLength q) (composedSeedAlgorithm q hq)

theorem composedCoreAlgorithm_depthBound (q : ℕ) (hq : 3 ≤ q) :
    (composedCoreAlgorithm q hq).DepthBound
      (3001 ^ 2 * seedLength q ^ 2 * composedSeedCost q) :=
  KleeneAlgorithms.algorithm_depthBound _ (seedLength_pos q) (composedSeedAlgorithm_depthBound q hq)

theorem composedCoreAlgorithm_error (q : ℕ) (hq : 3 ≤ q) (hodd : Odd q)
    (x : CoreCoordinates q × InnerCoordinates q → Bool) (b : Bool)
    (hdefined : (coreCertificates q).DefinedAt (fun t => inner q (fun u => x (t, u))) b) :
    (composedCoreAlgorithm q hq).probability (fun output => output ≠ b) x ≤ 1 / 100 :=
  KleeneAlgorithms.algorithm_error (ApproxIndex.value (ApproxIndex.seedRadius q)) (inner q)
    (composedSeedAlgorithm q hq) (seedLength_pos q) (composedSeedAlgorithm_error q hq hodd) x b hdefined

noncomputable def amplifiedCoreAlgorithm (q : ℕ) (hq : 3 ≤ q) (n : ℕ) :=
  (composedCoreAlgorithm q hq).amplify n

def composedCoreCost (q n : ℕ) : ℕ :=
  27 * 3 ^ n * (3001 ^ 2 * seedLength q ^ 2 * composedSeedCost q)

theorem amplifiedCoreAlgorithm_depthBound (q : ℕ) (hq : 3 ≤ q) (n : ℕ) :
    (amplifiedCoreAlgorithm q hq n).DepthBound (composedCoreCost q n) :=
  (composedCoreAlgorithm q hq).depthBound_amplify (composedCoreAlgorithm_depthBound q hq) n

theorem amplifiedCoreAlgorithm_error (q : ℕ) (hq : 3 ≤ q) (hodd : Odd q) (n : ℕ)
    (x : CoreCoordinates q × InnerCoordinates q → Bool) (b : Bool)
    (hdefined : (coreCertificates q).DefinedAt (fun t => inner q (fun u => x (t, u))) b) :
    (amplifiedCoreAlgorithm q hq n).probability (fun output => output ≠ b) x ≤
      (1 / 3 : ℝ) * (1 / 2 : ℝ) ^ (2 ^ n) :=
  (composedCoreAlgorithm q hq).probability_amplify_error b x
    ((composedCoreAlgorithm_error q hq hodd x b hdefined).trans (by norm_num)) n

noncomputable def outerVerifier (q c : ℕ) :
    (Fin c → Bool) → DecisionTree (OuterCoordinates q c) Bool :=
  KleeneVerifier.tree (ApproxIndex.value (ApproxIndex.seedRadius q)) (outerDecoder q c)

def outerVerifierCost (q c : ℕ) : ℕ := 36 * payloadWidth q c + c * seedLength q ^ 2

theorem outerVerifier_depth_le (q c : ℕ) (address : Fin c → Bool) :
    (outerVerifier q c address).depth ≤ outerVerifierCost q c := by
  have h := KleeneVerifier.tree_depth_le
    (ApproxIndex.value (k := ApproxIndex.seedSize q) (ApproxIndex.seedRadius q))
    (outerDecoder q c) address
  simpa only [Fintype.card_fin, seedLength, outerVerifierCost, pow_two, Nat.mul_assoc] using h

theorem outerVerifier_correct (q c : ℕ) (address : Fin c → Bool) (x : OuterCoordinates q c → Bool) :
    (outerVerifier q c address).eval x = true ↔
      (certificateInputOfBits x).AcceptsAt (coreCertificates q) (outerDecoder q c) address :=
  KleeneVerifier.tree_correct _ _ _ _

noncomputable def totalComposedAlgorithm (q c : ℕ) (hq : 3 ≤ q) (n : ℕ) :=
  CertificateAlgorithms.algorithm (inner q) (amplifiedCoreAlgorithm q hq n) (outerVerifier q c)

def totalComposedCost (q c n : ℕ) : ℕ :=
  c * composedCoreCost q n + outerVerifierCost q c * (q ^ 3 * cellWidth q)

theorem totalComposedAlgorithm_depthBound (q c : ℕ) (hq : 3 ≤ q) (n : ℕ) :
    (totalComposedAlgorithm q c hq n).DepthBound (totalComposedCost q c n) := by
  have h := CertificateAlgorithms.algorithm_depthBound (inner q) (amplifiedCoreAlgorithm q hq n)
    (outerVerifier q c) (amplifiedCoreAlgorithm_depthBound q hq n) (outerVerifier_depth_le q c)
  simpa only [Fintype.card_fin, card_innerCoordinates] using h

theorem totalComposedAlgorithm_error (q c : ℕ) (hq : 3 ≤ q) (hodd : Odd q) (n : ℕ)
    (x : OuterCoordinates q c × InnerCoordinates q → Bool) :
    (totalComposedAlgorithm q c hq n).probability
      (fun output => output ≠ comp (outer q c) (inner q) x) x ≤
      c * ((1 / 3 : ℝ) * (1 / 2 : ℝ) ^ (2 ^ n)) := by
  have h := CertificateAlgorithms.algorithm_error_le (coreCertificates q) (outerDecoder q c) (inner q)
    (amplifiedCoreAlgorithm q hq n) (outerVerifier q c) (outerVerifier_correct q c)
    ((1 / 3 : ℝ) * (1 / 2 : ℝ) ^ (2 ^ n)) (by positivity)
    (amplifiedCoreAlgorithm_error q hq hodd n) x
  simpa only [Fintype.card_fin] using h

/-- A fully instantiated upper bound in the original randomized-query model. -/
theorem R_comp_le_totalComposedCost (q c : ℕ) (hq : 3 ≤ q) (hodd : Odd q) (n : ℕ)
    (herror : (c : ℝ) * ((1 / 3 : ℝ) * (1 / 2 : ℝ) ^ (2 ^ n)) ≤ 1 / 3) :
    R (comp (outer q c) (inner q)) ≤ totalComposedCost q c n := by
  apply R_le_of_hasRandomizedBound
  apply (totalComposedAlgorithm q c hq n).toHasRandomizedBound
    (totalComposedAlgorithm_depthBound q c hq n)
  intro x
  have h := (totalComposedAlgorithm_error q c hq hodd n x).trans herror
  rw [FiniteRandomizedTree.probability_not] at h
  linarith

end QueryComplexity.Construction
