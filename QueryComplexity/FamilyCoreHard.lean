import QueryComplexity.Families
import QueryComplexity.CoreHardDistribution

/-! The explicit core hard distribution instantiated at the final family's
actual coordinate and certificate types. -/

namespace QueryComplexity.Construction

open FiniteProbability DirectProduct

theorem seedLength_pos (q : ℕ) : 0 < seedLength q := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨.inr ((fun _ => false), false)⟩

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

theorem R_coreExtension_gt (q : ℕ) (hq : 2 ≤ q) : coreQueryBudget q < R (coreExtension q) :=
  R_gt_of_hard_distribution (coreExtension q) (coreQueryBudget q) (coreWeight q)
    (coreWeight_nonnegative q) (coreWeight_mass q) (5 / 8) (by norm_num) (core_hardness q hq)

end QueryComplexity.Construction
