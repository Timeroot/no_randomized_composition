import QueryComplexity.PointerSearch
import QueryComplexity.PointerLayerSources
import QueryComplexity.ProductSourceAveraging

open scoped BigOperators

namespace QueryComplexity.PointerDistributions

open FiniteProbability ProductPosteriors

abbrev NegativeSample (q : ℕ) := Fin q → Fin q
abbrev PairedSource (q : ℕ) := PointerInput q × NegativeSample q

noncomputable def pairedSourceWeight (q : ℕ) (x : PairedSource q) : ℝ :=
  positiveWeight q x.1 * uniformWeight (NegativeSample q) x.2

def pairedSourceInput {q : ℕ} (b : Bool) (x : PairedSource q) : PointerInput q :=
  if b then x.1 else negative x.2

theorem pairedSource_pushforward (q : ℕ) (hq : 0 < q) (b : Bool) :
    pushforward (pairedSourceWeight q) (pairedSourceInput b) = selectedWeight q b := by
  classical
  letI : Nonempty (NegativeSample q) := ⟨id⟩
  funext x
  have hpos := positiveWeight_mass q hq
  have hneg := mass_uniformWeight (NegativeSample q)
  cases b
  · simp only [pushforward, Fintype.sum_prod_type, pairedSourceWeight, pairedSourceInput,
      Bool.false_eq_true, ↓reduceIte, selectedWeight]
    rw [Finset.sum_comm]
    simp only [negativeWeight, pushforward]
    apply Finset.sum_congr rfl
    intro h _
    by_cases he : negative h = x
    · simp only [if_pos he, ← Finset.sum_mul]
      change mass (positiveWeight q) * _ = _
      rw [hpos, one_mul]
    · simp [he]
  · simp only [pushforward, Fintype.sum_prod_type, pairedSourceWeight, pairedSourceInput,
      ↓reduceIte, selectedWeight]
    have he (p : PointerInput q) :
        (∑ h, if p = x then positiveWeight q p * uniformWeight (NegativeSample q) h else 0) =
        if p = x then positiveWeight q p else 0 := by
      by_cases hx : p = x
      · simp only [if_pos hx, ← Finset.mul_sum]
        change _ * mass (uniformWeight (NegativeSample q)) = _
        rw [hneg, mul_one]
      · simp [hx]
    simp_rw [he]
    simp

def hiddenCurry (q : ℕ) : ((Fin q × Fin q) → Fin q) ≃ (Fin q → NegativeSample q) where
  toFun h := fun i col => h (i, col)
  invFun h := fun p => h p.1 p.2
  left_inv h := rfl
  right_inv h := rfl

/-- Independent selected sources are obtained by averaging the fixed-positive
generation over positive inputs and uniform negative hidden rows. -/
theorem selectedProduct_expectation (q : ℕ) (hq : 0 < q)
    (z : Fin q → Bool) (φ : BlockInput q → ℝ) :
    (∑ x, selectedProduct q z x * φ x) =
      ∑ positiveInputs, jointWeight (fun _ : Fin q => positiveWeight q) positiveInputs *
        average (fun hidden : (Fin q × Fin q) → Fin q =>
          φ (fixedLabelInput z positiveInputs hidden)) := by
  calc
    _ = ∑ x : Fin q → PairedSource q, jointWeight (fun _ => pairedSourceWeight q) x *
        φ (fun i => pairedSourceInput (z i) (x i)) := by
      have h := joint_pushforward_expectation (fun _ : Fin q => pairedSourceWeight q)
        (fun i => pairedSourceInput (z i)) φ
      simpa only [pairedSource_pushforward q hq, selectedProduct] using h
    _ = ∑ positiveInputs, jointWeight (fun _ : Fin q => positiveWeight q) positiveInputs *
        average (fun hidden : Fin q → NegativeSample q =>
          φ (fun i => if z i then positiveInputs i else negative (hidden i))) := by
      exact product_source_expectation (positiveWeight q)
        (fun positives hidden => φ (fun i => if z i then positives i else negative (hidden i)))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro positives _
      congr 1
      exact (average_equiv (hiddenCurry q)
        (fun hidden => φ (fun i => if z i then positives i else negative (hidden i)))).symm

theorem selectedProduct_expectation_le (q : ℕ) (hq : 0 < q)
    (z : Fin q → Bool) (φ : BlockInput q → ℝ) (M : ℝ)
    (hbound : ∀ positiveInputs, average (fun hidden : (Fin q × Fin q) → Fin q =>
      φ (fixedLabelInput z positiveInputs hidden)) ≤ M) :
    (∑ x, selectedProduct q z x * φ x) ≤ M := by
  rw [selectedProduct_expectation q hq z φ]
  calc
    _ ≤ ∑ positives, jointWeight (fun _ : Fin q => positiveWeight q) positives * M :=
      Finset.sum_le_sum fun positives _ => mul_le_mul_of_nonneg_left (hbound positives)
        (jointWeight_nonnegative _ (fun _ => positiveWeight_nonnegative q) positives)
    _ = M := by
      rw [← Finset.sum_mul]
      change mass (jointWeight (fun _ : Fin q => positiveWeight q)) * M = M
      rw [jointWeight_mass]
      simp only [positiveWeight_mass q hq, Finset.prod_const_one, one_mul]

end QueryComplexity.PointerDistributions
