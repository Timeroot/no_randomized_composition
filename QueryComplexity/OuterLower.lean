import QueryComplexity.FamilyListDPT
import QueryComplexity.CheatSheetHybrid

open scoped BigOperators

namespace QueryComplexity.Construction

open FiniteProbability DirectProduct CellProjection CheatSheetHybrid

set_option maxHeartbeats 1000000

local instance coreInputFintype (q : ℕ) : Fintype (CoreCoordinates q → Bool) := inferInstance

noncomputable def outerListIndicator (q ell : ℕ)
    (tree : DecisionTree (OuterCoordinates q (100 * ell)) Bool)
    (cells : OuterCells q ell) (cores : Fin (100 * ell) → CoreCoordinates q → Bool) : ℝ := by
  classical
  exact if ∃ j, (outerListTree q ell tree cells).eval (fun p => cores p.1 p.2) j =
    (fun i => coreExtension q (cores i)) then 1 else 0

theorem outerListIndicator_nonnegative (q ell : ℕ)
    (tree : DecisionTree (OuterCoordinates q (100 * ell)) Bool)
    (cells : OuterCells q ell) (cores : Fin (100 * ell) → CoreCoordinates q → Bool) :
    0 ≤ outerListIndicator q ell tree cells cores := by
  classical
  unfold outerListIndicator
  split_ifs <;> norm_num

theorem outerListScore_eq (q ell : ℕ)
    (tree : DecisionTree (OuterCoordinates q (100 * ell)) Bool) (cells : OuterCells q ell) :
    listScore (coreExtension q) (outerListTree q ell tree cells) (fun _ => coreWeight q) =
      ∑ cores, jointWeight (fun _ : Fin (100 * ell) => coreWeight q) cores *
        outerListIndicator q ell tree cells cores := by
  classical
  simp only [listScore, outerListIndicator, mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr rfl
  intro cores _
  congr 1

theorem outerListIndicator_heavy (q ell : ℕ)
    (tree : DecisionTree (OuterCoordinates q (100 * ell)) Bool)
    (hdepth : tree.depth ≤ outerQueryBudget q ell)
    (cells : OuterCells q ell) (cores : Fin (100 * ell) → CoreCoordinates q → Bool) :
    (if outerCellThreshold q ell < DecisionTree.ownerCount cellOwner tree
      (fun i => coreExtension q (cores i)) (certificateBitsOfInput ⟨cores, cells⟩)
      then (1 : ℝ) else 0) ≤ outerListIndicator q ell tree cells cores := by
  classical
  split_ifs with h
  · have hm := coreListTree_contains_owner (outerCellThreshold q ell) (q ^ 3)
      (outerQueryBudget q ell) tree hdepth (outer_list_capacity q ell) cores cells
      (fun i => coreExtension q (cores i)) h
    simpa only [outerListIndicator, outerListTree, hm, if_true] using (le_refl (1 : ℝ))
  · exact outerListIndicator_nonnegative q ell tree cells cores

/-- The actual total encoded cheat-sheet function has no randomized algorithm
at the claimed query budget. The invalid cell-array distribution is fixed
independently of the product-distributed core inputs. -/
theorem outer_no_randomized_bound (q ell : ℕ) (hq : 2 ≤ q)
    (hell : 1 ≤ ell) (hpow : q ≤ 2 ^ ell) :
    ¬ HasRandomizedBound (outer q (100 * ell)) (outerQueryBudget q ell) := by
  classical
  rintro ⟨m, trees, weights, hdepth, hweight, hsum, hcorrect⟩
  let A : FiniteRandomizedTree (Fin m) (OuterCoordinates q (100 * ell)) Bool :=
    ⟨trees, weights, hweight, hsum⟩
  let a := payloadWidth q (100 * ell)
  have ha : 0 < a := by dsimp [a, payloadWidth]; omega
  let D : (Fin a → Bool) → Bool × (Fin (100 * ell) → Witness q) :=
    finiteDecode a (certificatePayload_card_bound (seedLength q) (100 * ell))
  let w₀ : Fin (100 * ell) → Witness q := fun _ => Sum.inl id
  obtain ⟨u, hu⟩ := finiteDecode_surjective a
    (certificatePayload_card_bound (seedLength q) (100 * ell)) (false, w₀)
  change D u = (false, w₀) at hu
  obtain ⟨z₀, hz₀⟩ := BinaryCode.privateDecoder_surjective a ha u
  letI : Nonempty (CellFiber a ha u) := ⟨⟨z₀, hz₀⟩⟩
  let Z := (Fin (100 * ell) → Bool) → CellFiber a ha u
  let μ := jointWeight (fun _ : Fin (100 * ell) => coreWeight q)
  have hμ : Nonnegative μ := jointWeight_nonnegative (fun _ => coreWeight_nonnegative q)
  have hmass : mass μ = 1 := by
    simp only [μ, jointWeight_mass, coreWeight_mass, Finset.prod_const_one]
  have hc : ∀ x, (2 : ℝ) / 3 ≤ A.probability
      (fun b => b = certificateBoolFn (coreCertificates q)
        (fun z => D (BinaryCode.privateDecoder a ha z)) x) x := by
    intro x
    simpa only [A, FiniteRandomizedTree.probability, outer, outerDecoder,
      privateAlphabetDecoder, Function.comp_apply, D, a] using hcorrect x
  have hpoint (cores : Fin (100 * ell) → CoreCoordinates q → Bool) (hsupport : μ cores ≠ 0) :
      (1 : ℝ) / 6 ≤ ∑ s, A.weight s * average (fun z : Z =>
        outerListIndicator q ell (A.tree s) (rawCells z) cores) := by
    have hi (i : Fin (100 * ell)) : coreWeight q (cores i) ≠ 0 := by
      intro heq
      apply hsupport
      exact Finset.prod_eq_zero (Finset.mem_univ i) heq
    choose w hw using fun i => coreWeight_certified q (cores i) (hi i)
    obtain ⟨v, hv⟩ := finiteDecode_surjective a
      (certificatePayload_card_bound (seedLength q) (100 * ell)) (true, w)
    have hh := heavy_probability a ha D (coreCertificates q) A hc cores
      (fun i => coreExtension q (cores i)) w w₀ hw u v hu hv
    apply hh.trans
    apply Finset.sum_le_sum
    intro s _
    apply mul_le_mul_of_nonneg_left _ (A.weight_nonneg s)
    apply average_le
    intro z
    exact outerListIndicator_heavy q ell (A.tree s) (hdepth s) (rawCells z) cores
  have hlower : (1 : ℝ) / 6 ≤ ∑ cores, μ cores *
      (∑ s, A.weight s * average (fun z : Z =>
        outerListIndicator q ell (A.tree s) (rawCells z) cores)) := by
    calc
      _ = ∑ cores, μ cores * ((1 : ℝ) / 6) := by
        rw [← Finset.sum_mul]
        change (1 : ℝ) / 6 = mass μ * (1 / 6)
        rw [hmass, one_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro cores _
        by_cases hz : μ cores = 0
        · simp only [hz, zero_mul, le_refl]
        · exact mul_le_mul_of_nonneg_left (hpoint cores hz) (hμ cores)
  have hswap : (∑ cores, μ cores *
      (∑ s, A.weight s * average (fun z : Z =>
        outerListIndicator q ell (A.tree s) (rawCells z) cores))) =
      ∑ s, A.weight s * average (fun z : Z =>
        listScore (coreExtension q) (outerListTree q ell (A.tree s) (rawCells z))
          (fun _ => coreWeight q)) := by
    simp only [outerListScore_eq, average_sum, average_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro cores _
    ring
  rw [hswap] at hlower
  have hupper : (∑ s, A.weight s * average (fun z : Z =>
      listScore (coreExtension q) (outerListTree q ell (A.tree s) (rawCells z))
        (fun _ => coreWeight q))) ≤ (1 : ℝ) / 12 := by
    calc
      _ ≤ ∑ s, A.weight s * ((1 : ℝ) / 12) := by
        apply Finset.sum_le_sum
        intro s _
        apply mul_le_mul_of_nonneg_left _ (A.weight_nonneg s)
        have havg := average_le (fun z : Z =>
          outerListTree_success_le q ell hq hell hpow (A.tree s) (hdepth s) (rawCells z))
        simpa only [average_const] using havg
      _ = _ := by rw [← Finset.sum_mul, A.weight_sum, one_mul]
  linarith

theorem R_outer_gt (q ell : ℕ) (hq : 2 ≤ q) (hell : 1 ≤ ell) (hpow : q ≤ 2 ^ ell) :
    outerQueryBudget q ell < R (outer q (100 * ell)) := by
  by_contra h
  exact outer_no_randomized_bound q ell hq hell hpow
    (hasRandomizedBound_iff_R_le.mpr (Nat.le_of_not_gt h))

end QueryComplexity.Construction
