import QueryComplexity.FamilyCoreHard
import QueryComplexity.CellProjection
import QueryComplexity.DirectProductNumerics

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

theorem outerListTree_contains (q ell : ℕ)
    (tree : DecisionTree (OuterCoordinates q (100 * ell)) Bool)
    (hdepth : tree.depth ≤ outerQueryBudget q ell)
    (cores : Fin (100 * ell) → CoreCoordinates q → Bool) (cells : OuterCells q ell)
    (target : Fin (100 * ell) → Bool)
    (hheavy : outerCellThreshold q ell < (projectCell tree cores cells target).queryCost (cells target)) :
    ∃ j : Fin (q ^ 3), (outerListTree q ell tree cells).eval (fun p => cores p.1 p.2) j = target :=
  coreListTree_contains _ _ _ tree hdepth (outer_list_capacity q ell) cores cells target hheavy

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

/-- Randomizing both the original algorithm and the fixed physical cell
array preserves the same upper bound; the core distribution is independent. -/
theorem randomized_outerListTree_success_le (q ell : ℕ) (hq : 2 ≤ q)
    (hell : 1 ≤ ell) (hpow : q ≤ 2 ^ ell)
    {A : Type*} [Fintype A]
    (trees : A → DecisionTree (OuterCoordinates q (100 * ell)) Bool)
    (cells : A → OuterCells q ell) (weight : A → ℝ)
    (hweight : ∀ a, 0 ≤ weight a) (hsum : ∑ a, weight a = 1)
    (hdepth : ∀ a, (trees a).depth ≤ outerQueryBudget q ell) :
    (∑ a, weight a * listScore (coreExtension q) (outerListTree q ell (trees a) (cells a))
      (fun _ => coreWeight q)) ≤ 1 / 12 := by
  calc
    _ ≤ ∑ a, weight a * ((1 : ℝ) / 12) := Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_left
        (outerListTree_success_le q ell hq hell hpow (trees a) (hdepth a) (cells a)) (hweight a)
    _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]

end QueryComplexity.Construction
