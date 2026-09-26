import Main.Construction
import QueryComplexity.ApproxIndex.AndOrLower
import QueryComplexity.LowerBounds.DirectProduct
import QueryComplexity.CheatSheet.CellProjection
import QueryComplexity.CheatSheet.Hybrid

/-! The outer lower bound. We instantiate the approximate-index AND--OR hard
distribution, amplify it across a list of copies, and transfer the bound through
the private-cell encoding and cheat-sheet construction. -/

namespace QueryComplexity.CoreLower

open FiniteProbability DirectProduct ApproxIndex DecisionTree

variable {Row Col : Type*} [Fintype Row] [Fintype Col] [DecidableEq Row] [DecidableEq Col]

def coreBudget (Row Col : Type*) [Fintype Row] [Fintype Col] (q : ℕ) : ℕ :=
  Fintype.card Row * Fintype.card Col * q ^ 3

theorem numeric_hardness [Nonempty Row] [Nonempty Col] (q : ℕ) (hq : 2 ≤ q)
    (tree : DecisionTree (Coordinates Row Col (seedSize q)) Bool)
    (hdepth : tree.depth ≤ coreBudget Row Col q) :
    score extension (hardWeight (seedRadius q)) tree ≤ (5 : ℝ) / 8 := by
  have hqpos : 0 < q := by omega
  have hb : 0 < seedBudget q := by unfold seedBudget; positivity
  have h := hardWeight_score_le (seedRadius q) (seedBudget q) (coreBudget Row Col q) (seedEta q)
    hb (seedEta_nonnegative q) (seed_ballSliceBound q hqpos) tree hdepth
  have he : (coreBudget Row Col q : ℝ) /
      ((seedBudget q : ℝ) * ((Fintype.card Row : ℝ) * Fintype.card Col)) = 1 / 250 := by
    have hr : (Fintype.card Row : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hc : (Fintype.card Col : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hqpos
    simp only [coreBudget, seedBudget, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  have heta : (seedBudget q : ℝ) * seedEta q ≤ 16 / 135 := by
    rw [seedBudget_mul_eta q hqpos]
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 135 * q)).2
    nlinarith
  rw [he] at h
  linarith

end QueryComplexity.CoreLower

/-! The explicit core hard distribution instantiated at the final family's
actual coordinate and certificate types. -/

namespace QueryComplexity.Construction

open FiniteProbability DirectProduct

noncomputable def coreExtension (q : ℕ) : BoolFn (CoreCoordinates q) :=
  CoreLower.extension

noncomputable def coreWeight (q : ℕ) : Weight (CoreCoordinates q → Bool) :=
  CoreLower.hardWeight (ApproxIndex.seedRadius q)

def coreQueryBudget (q : ℕ) : ℕ := seedLength q * seedLength q * q ^ 3

theorem coreWeight_nonnegative (q : ℕ) : Nonnegative (coreWeight q) :=
  CoreLower.hardWeight_nonnegative _

theorem coreWeight_mass (q : ℕ) : mass (coreWeight q) = 1 := by
  letI : Nonempty (Fin (seedLength q)) := ⟨⟨0, seedLength_pos q⟩⟩
  exact CoreLower.mass_hardWeight _

theorem core_hardness (q : ℕ) (hq : 2 ≤ q)
    (tree : DecisionTree (CoreCoordinates q) Bool) (hdepth : tree.depth ≤ coreQueryBudget q) :
    score (coreExtension q) (coreWeight q) tree ≤ (5 : ℝ) / 8 := by
  letI : Nonempty (Fin (seedLength q)) := ⟨⟨0, seedLength_pos q⟩⟩
  apply CoreLower.numeric_hardness q hq tree
  simpa [CoreLower.coreBudget, coreQueryBudget] using hdepth

theorem core_hardness_two_thirds (q : ℕ) (hq : 2 ≤ q)
    (tree : DecisionTree (CoreCoordinates q) Bool) (hdepth : tree.depth ≤ coreQueryBudget q) :
    score (coreExtension q) (coreWeight q) tree ≤ (2 : ℝ) / 3 :=
  (core_hardness q hq tree hdepth).trans (by norm_num)

/-- Every input in the support of the hard distribution has a valid core
certificate for the exact Boolean value used by the direct-product theorem. -/
theorem coreWeight_certified (q : ℕ) (x : CoreCoordinates q → Bool)
    (h : coreWeight q x ≠ 0) :
    (coreCertificates q).DefinedAt x (coreExtension q x) := by
  exact CoreLower.hardWeight_supported (ApproxIndex.seedRadius q) x h

end QueryComplexity.Construction

/-! The outer-family lower bound. Integer-power estimates control the
strong direct-product list bound; a coded-cell hybrid then rules out a
randomized algorithm below the claimed query budget. -/

namespace QueryComplexity.DirectProduct

theorem four_copy_decay (h : ℕ) :
    (2 : ℝ) ^ h * ((2 : ℝ) / 3) ^ (4 * h) ≤ ((1 : ℝ) / 2) ^ h := by
  rw [pow_mul, ← mul_pow]
  apply pow_le_pow_left₀ (by norm_num)
  norm_num

theorem quotient_budget_le (ell A Q : ℕ) (hQ : Q ≤ 25 * ell * A) :
    Q / (A + 1) ≤ 25 * ell := by
  apply (Nat.div_le_iff_le_mul_add_pred (Nat.succ_pos A)).2
  nlinarith

/-- The chosen number of copies makes the direct-product list bound smaller
than the `1/6` inclusion probability supplied by the coded-cell hybrid. -/
theorem list_bound_small (ell q A Q L : ℕ) (hell : 1 ≤ ell)
    (hq : q ≤ 2 ^ ell) (hQ : Q ≤ 25 * ell * A) (hL : L ≤ q ^ 3) :
    (L : ℝ) * ((2 : ℝ) ^ (Q / (A + 1)) * ((2 : ℝ) / 3) ^ (100 * ell)) ≤ 1 / 16 := by
  have hquot := quotient_budget_le ell A Q hQ
  have hqR : (q : ℝ) ≤ (2 : ℝ) ^ ell := by exact_mod_cast hq
  have hL' : (L : ℝ) ≤ (2 : ℝ) ^ (3 * ell) := by
    calc
      _ ≤ (q : ℝ) ^ 3 := by exact_mod_cast hL
      _ ≤ ((2 : ℝ) ^ ell) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hqR 3
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hdecay : (2 : ℝ) ^ (25 * ell) * ((2 : ℝ) / 3) ^ (100 * ell) ≤
      ((1 : ℝ) / 2) ^ (25 * ell) := by
    simpa only [show 4 * (25 * ell) = 100 * ell by omega] using four_copy_decay (25 * ell)
  have hpow : (2 : ℝ) ^ (Q / (A + 1)) ≤ (2 : ℝ) ^ (25 * ell) :=
    pow_le_pow_right₀ (by norm_num) hquot
  calc
    _ ≤ (L : ℝ) * ((2 : ℝ) ^ (25 * ell) * ((2 : ℝ) / 3) ^ (100 * ell)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpow (by positivity)) (Nat.cast_nonneg _)
    _ ≤ (L : ℝ) * ((1 : ℝ) / 2) ^ (25 * ell) :=
      mul_le_mul_of_nonneg_left hdecay (Nat.cast_nonneg _)
    _ ≤ (2 : ℝ) ^ (3 * ell) * ((1 : ℝ) / 2) ^ (25 * ell) :=
      mul_le_mul_of_nonneg_right hL' (by positivity)
    _ = ((1 : ℝ) / 2) ^ (22 * ell) := by
      rw [show 25 * ell = 3 * ell + 22 * ell by omega, pow_add]
      rw [← mul_assoc, ← mul_pow]
      norm_num
    _ ≤ ((1 : ℝ) / 2) ^ 4 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ = _ := by norm_num

theorem list_bound_twelfth (ell q A Q L : ℕ) (hell : 1 ≤ ell)
    (hq : q ≤ 2 ^ ell) (hQ : Q ≤ 25 * ell * A) (hL : L ≤ q ^ 3) :
    (L : ℝ) * ((2 : ℝ) ^ (Q / (A + 1)) * ((2 : ℝ) / 3) ^ (100 * ell)) ≤ 1 / 12 :=
  (list_bound_small ell q A Q L hell hq hQ hL).trans (by norm_num)

end QueryComplexity.DirectProduct

/-! The extracted cell-list algorithm meets the strong direct-product bound
for the concrete family. -/

open scoped BigOperators

namespace QueryComplexity.Construction

open FiniteProbability DirectProduct DecisionTree CellProjection

def outerQueryBudget (q ell : ℕ) : ℕ := 25 * ell * coreQueryBudget q
def outerCellThreshold (q ell : ℕ) : ℕ := 12 * payloadWidth q (100 * ell)

abbrev OuterCells (q ell : ℕ) :=
  (Fin (100 * ell) → Bool) → Fin (36 * payloadWidth q (100 * ell)) → Bool

theorem outer_list_capacity (q ell : ℕ) :
    outerQueryBudget q ell / (outerCellThreshold q ell + 1) ≤ q ^ 3 := by
  have hthreshold : 25 * ell * (seedLength q * seedLength q) ≤ outerCellThreshold q ell + 1 := by
    unfold outerCellThreshold payloadWidth
    nlinarith [Nat.zero_le (ell * (seedLength q * seedLength q))]
  have hmul := Nat.mul_le_mul_right (q ^ 3) hthreshold
  have hQ : outerQueryBudget q ell ≤ (outerCellThreshold q ell + 1) * q ^ 3 := by
    simpa only [outerQueryBudget, coreQueryBudget, Nat.mul_assoc] using hmul
  apply (Nat.div_le_iff_le_mul_add_pred (Nat.succ_pos _)).2
  nlinarith

noncomputable def outerListTree (q ell : ℕ)
    (tree : DecisionTree (OuterCoordinates q (100 * ell)) Bool) (cells : OuterCells q ell) :
    DecisionTree (Fin (100 * ell) × CoreCoordinates q) (Fin (q ^ 3) → Fin (100 * ell) → Bool) :=
  coreListTree (outerCellThreshold q ell) (q ^ 3) tree cells

theorem outerListTree_depth_le (q ell : ℕ)
    (tree : DecisionTree (OuterCoordinates q (100 * ell)) Bool) (cells : OuterCells q ell) :
    (outerListTree q ell tree cells).depth ≤ tree.depth :=
  coreListTree_depth_le _ _ _ _

/-- For every fixed physical cell array and every original decision tree of
the proposed lower-bound depth, the extracted candidate list contains the
independent cores' true answer vector with probability at most `1/12`. -/
theorem outerListTree_success_le (q ell : ℕ) (hq : 2 ≤ q) (hell : 1 ≤ ell) (hpow : q ≤ 2 ^ ell)
    (tree : DecisionTree (OuterCoordinates q (100 * ell)) Bool)
    (hdepth : tree.depth ≤ outerQueryBudget q ell) (cells : OuterCells q ell) :
    listScore (coreExtension q) (outerListTree q ell tree cells) (fun _ => coreWeight q) ≤ 1 / 12 := by
  have hdpt := list_direct_product (coreExtension q) (coreQueryBudget q) (outerQueryBudget q ell)
    ((2 : ℝ) / 3) (outerListTree q ell tree cells) (fun _ => coreWeight q)
    (fun _ => coreWeight_nonnegative q) (by norm_num)
    (fun _ single hs => core_hardness_two_thirds q hq single hs)
    ((outerListTree_depth_le q ell tree cells).trans hdepth)
  have hnum := list_bound_twelfth ell q (coreQueryBudget q) (outerQueryBudget q ell) (q ^ 3)
    hell hpow (le_refl _) (le_refl _)
  exact hdpt.trans (by simpa only [Fintype.card_fin] using hnum)

end QueryComplexity.Construction

open FiniteEncoding

open scoped BigOperators

namespace QueryComplexity.Construction

open FiniteProbability DirectProduct CellProjection CheatSheetHybrid

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
  refine Finset.sum_congr rfl fun cores _ => ?_
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

set_option maxHeartbeats 1000000 in
-- Combining the nested finite averages with the list bound needs extra elaboration time.
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
    refine Finset.sum_le_sum fun s _ => ?_
    apply mul_le_mul_of_nonneg_left _ (A.weight_nonneg s)
    apply average_le
    intro z
    exact outerListIndicator_heavy q ell (A.tree s) (hdepth s) (rawCells z) cores
  have hlower : (1 : ℝ) / 6 ≤ ∑ cores, μ cores *
      (∑ s, A.weight s * average (fun z : Z =>
        outerListIndicator q ell (A.tree s) (rawCells z) cores)) := by
    calc
      _ = ∑ cores, μ cores * ((1 : ℝ) / 6) := by
        rw [← Finset.sum_mul, ← mass, hmass, one_mul]
      _ ≤ _ := by
        refine Finset.sum_le_sum fun cores _ => ?_
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
    refine Finset.sum_congr rfl fun s _ => ?_
    refine Finset.sum_congr rfl fun cores _ => ?_
    ring
  rw [hswap] at hlower
  have hupper : (∑ s, A.weight s * average (fun z : Z =>
      listScore (coreExtension q) (outerListTree q ell (A.tree s) (rawCells z))
        (fun _ => coreWeight q))) ≤ (1 : ℝ) / 12 := by
    calc
      _ ≤ ∑ s, A.weight s * ((1 : ℝ) / 12) := by
        refine Finset.sum_le_sum fun s _ => ?_
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

namespace QueryComplexity.Construction

/-- Explicit lower bound for the actual reindexed total outer family. -/
theorem R_F_gt (n : ℕ) :
    25 * scale n * (seedLength (pointerArity n) * seedLength (pointerArity n) * pointerArity n ^ 3)
      < R (F n) := by
  rw [F, R_toFin]
  exact R_outer_gt (pointerArity n) (scale n)
    ((by omega : 2 ≤ 3).trans (pointerArity_ge_three n))
    ((by omega : 1 ≤ 10).trans (scale_ge_ten n)) (pointerArity_le_pow_scale n)

theorem R_F_lower (n : ℕ) :
    25 * scale n * (seedLength (pointerArity n) * seedLength (pointerArity n) * pointerArity n ^ 3)
      ≤ R (F n) := (R_F_gt n).le

end QueryComplexity.Construction
