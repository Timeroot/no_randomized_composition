import QueryComplexity.PointerFunction.Majority.Search
import QueryComplexity.PointerFunction.Majority.LeafLaws
import Main.InnerNumerics
import QueryComplexity.PointerFunction.Majority.Layers
import QueryComplexity.Encoding.RandomizedLowerBound
import Main.Construction

/-! The inner-family lower bound. Posterior variance bounds the success of
cell-query algorithms, and the private encoding transfers this hardness
to the concrete total Boolean function. -/

namespace QueryComplexity.PointerDistributions

open scoped BigOperators
open FiniteProbability

attribute [local instance] Classical.propDecidable

theorem negativeBlocks_count (q k : ℕ) (z : Fin q → Bool)
    (hz : (BoolCounting.trueSet z).card = k) (hk : 2 * k ≤ q + 1) :
    q ≤ 2 * (Finset.univ.filter (fun i => z i = false)).card + 1 := by
  have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : Fin q => z i = true)
  have heq : (Finset.univ.filter (fun i : Fin q => ¬ z i = true)) =
      Finset.univ.filter (fun i => z i = false) := by
    ext i
    simp
  rw [heq, Finset.card_univ, Fintype.card_fin] at hsum
  have htrue : (Finset.univ.filter (fun i : Fin q => z i = true)).card = k := hz
  omega

/-- The exceptional posterior-variance event is small under either central
count layer; its probability is charged directly under that layer. -/
theorem layer_bad_variance_bound {q r : ℕ} {Output : Type*} (hq : 5 ≤ q) (hr : 0 < r)
    (hrsmall : 4 * r ≤ q) (tree : BlockCellTree q Output) (k : ℕ)
    (hk : k ≤ q) (hkcentral : 2 * k ≤ q + 1) :
    (∑ x : BlockInput q, layerWeight q k x *
      (if varianceGood tree ((q : ℝ) / (16 * (5 : ℝ) ^ r)) x then (0 : ℝ) else 1)) ≤
      (2 * tree.depth / q) / ((q : ℝ) * r / 8) := by
  apply layerWeight_expectation_le q k hk
  intro z hz
  apply selectedProduct_expectation_le q (by omega) z
  intro positives
  exact fixedLabel_bad_variance_bound hq hr hrsmall tree z
    (negativeBlocks_count q k z hz hkcentral) positives

theorem layer_bad_variance_le_one_fiftieth (s : ℕ) (hs : 1000 ≤ s) {Output : Type*}
    (tree : BlockCellTree (PointerLowerNumerics.arity s) Output)
    (hdepth : tree.depth ≤ PointerLowerNumerics.cellBudget s)
    (k : ℕ) (hk : k ≤ PointerLowerNumerics.arity s)
    (hkcentral : 2 * k ≤ PointerLowerNumerics.arity s + 1) :
    (∑ x : BlockInput (PointerLowerNumerics.arity s),
      layerWeight (PointerLowerNumerics.arity s) k x *
        (if varianceGood tree (PointerLowerNumerics.varianceBound s) x then (0 : ℝ) else 1)) ≤
      (1 : ℝ) / 50 := by
  have hq : 5 ≤ PointerLowerNumerics.arity s := by
    have h := Nat.lt_two_pow_self (n := s)
    unfold PointerLowerNumerics.arity
    omega
  have h := layer_bad_variance_bound hq (PointerLowerNumerics.cutoff_pos s hs)
    (PointerLowerNumerics.cutoff_le_arity s hs) tree k hk hkcentral
  apply h.trans
  apply le_trans _ (PointerLowerNumerics.discovery_markov_le s hs)
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hdepth) (by norm_num)

theorem layer_leaf_bad_variance_eq {q : ℕ} {Output : Type*}
    (tree : BlockCellTree q Output) (k : ℕ) (v : ℝ) :
    (∑ leaf, if v ≤ PosteriorMajority.variance (leafPosterior tree leaf)
      then 0 else layerLeafWeight tree k leaf) =
      ∑ x : BlockInput q, layerWeight q k x * (if varianceGood tree v x then (0 : ℝ) else 1) := by
  have h := layerLeafWeight_event tree k
    (fun leaf => ¬ v ≤ PosteriorMajority.variance (leafPosterior tree leaf))
  simpa only [ite_not, mul_ite, mul_zero, mul_one, varianceGood, leafPosterior] using h

/-- An explicit adjacent-layer distribution defeats every cell-query tree
below the stated budget. All adaptive and posterior estimates are internal. -/
theorem pointer_majority_cell_hard (s m : ℕ) (hs : 1000 ≤ s)
    (hq : PointerLowerNumerics.arity s = 2 * m + 1)
    (tree : BlockCellTree (2 * m + 1) Bool)
    (hdepth : tree.depth ≤ PointerLowerNumerics.cellBudget s) :
    (∑ x : BlockInput (2 * m + 1),
      if tree.eval (blockRead x) = cellMajority (2 * m + 1) x
        then majorityHardWeight m x else 0) ≤ (3 : ℝ) / 5 := by
  have hb (k : ℕ) (hk : k ≤ 2 * m + 1) (hkc : 2 * k ≤ (2 * m + 1) + 1) :
      (∑ leaf, if PointerLowerNumerics.varianceBound s ≤
        PosteriorMajority.variance (leafPosterior tree leaf)
        then 0 else layerLeafWeight tree k leaf) ≤ (1 : ℝ) / 50 := by
    rw [layer_leaf_bad_variance_eq]
    have h := @layer_bad_variance_le_one_fiftieth s hs Bool
    rw [hq] at h
    exact h tree hdepth k hk hkc
  have hscore := majority_tree_success_le_layers m tree (PointerLowerNumerics.varianceBound s)
    ((1 : ℝ) / 50) ((1 : ℝ) / 50) (PointerLowerNumerics.varianceBound_pos s hs)
    (hb m (by omega) (by omega)) (hb (m + 1) (by omega) (by omega))
  have hm : 1 ≤ m := by
    have h := PointerLowerNumerics.exponential_margin s hs
    have hpow : 0 < 25 ^ PointerLowerNumerics.cutoff s := by positivity
    omega
  have hπ := BernoulliSmoothing.fairBinomialMass_pos (2 * m + 1) m (by omega)
  have hsquare := BernoulliSmoothing.fairBinomialMass_odd_square_lower m hm
  have hinv := PointerLowerNumerics.inverse_variance_prior_le s m hs hq
    (BernoulliSmoothing.fairBinomialMass (2 * m + 1) m) hπ.le hsquare
  exact hscore.trans (by grind)

end QueryComplexity.PointerDistributions

open FiniteEncoding

open scoped BigOperators

namespace QueryComplexity.PointerDistributions

open FiniteProbability Construction CodedOracleSimulation

abbrev FlatCoordinates (q : ℕ) := Fin q × (Fin q × Fin q)

def blockCellEquiv (q : ℕ) : BlockInput q ≃ (FlatCoordinates q → PointerCell q) where
  toFun x p := x p.1 p.2.1 p.2.2
  invFun s i row col := s (i, (row, col))
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def flatMajority (q : ℕ) (s : FlatCoordinates q → PointerCell q) : Bool :=
  cellMajority q ((blockCellEquiv q).symm s)

noncomputable def flatHardWeight (m : ℕ) : Weight (FlatCoordinates (2 * m + 1) → PointerCell (2 * m + 1)) :=
  pushforward (majorityHardWeight m) (blockCellEquiv (2 * m + 1))

theorem flatHardWeight_nonnegative (m : ℕ) : Nonnegative (flatHardWeight m) :=
  pushforward_nonnegative (majorityHardWeight_nonnegative m) _

theorem flatHardWeight_mass (m : ℕ) : mass (flatHardWeight m) = 1 := by
  rw [flatHardWeight, mass_pushforward, majorityHardWeight_mass]

theorem flatHardWeight_score (m : ℕ)
    (tree : OracleTree (FlatCoordinates (2 * m + 1)) (PointerCell (2 * m + 1)) Bool) :
    OracleOptimization.score (flatMajority (2 * m + 1)) (flatHardWeight m) tree =
      ∑ x : BlockInput (2 * m + 1),
        if tree.eval (blockCellEquiv (2 * m + 1) x) = cellMajority (2 * m + 1) x
          then majorityHardWeight m x else 0 := by
  classical
  have h := sum_pushforward_mul (majorityHardWeight m) (blockCellEquiv (2 * m + 1))
    (fun s => if tree.eval s = flatMajority (2 * m + 1) s then (1 : ℝ) else 0)
  simpa only [OracleOptimization.score, flatHardWeight, flatMajority, Equiv.symm_apply_apply,
    mul_ite, mul_one, mul_zero] using h

def encodedCoordinatesEquiv (q a : ℕ) :
    FlatCoordinates q × Fin (36 * a) ≃ Fin q × ((Fin q × Fin q) × Fin (36 * a)) :=
  Equiv.prodAssoc _ _ _

theorem inner_eq_reindex (q : ℕ) :
    inner q = reindex (encodedCoordinatesEquiv q (pointerPayloadWidth q))
      (blockEncoded (flatMajority q) (pointerDecoder q)) := rfl

/-- Any distributional lower bound against full pointer-cell queries lifts
to the concrete total Boolean inner function, with the proved coding factor. -/
theorem R_inner_lower_of_cell_bound (m B : ℕ) (β : ℝ) (hβ : β < 2 / 3)
    (hhard : ∀ tree : OracleTree (FlatCoordinates (2 * m + 1)) (PointerCell (2 * m + 1)) Bool,
      tree.depth ≤ B →
      (∑ x : BlockInput (2 * m + 1),
        if tree.eval (blockCellEquiv (2 * m + 1) x) = cellMajority (2 * m + 1) x
          then majorityHardWeight m x else 0) ≤ β) :
    (B + 1) * (12 * pointerPayloadWidth (2 * m + 1) + 1) ≤ R (inner (2 * m + 1)) := by
  classical
  let q := 2 * m + 1
  let a := pointerPayloadWidth q
  have ha : 0 < a := by dsimp [a, pointerPayloadWidth]; omega
  let D : (Fin a → Bool) → PointerCell q := finiteDecode a (pointerCell_card_bound q)
  choose payload hpayload using finiteDecode_surjective a (pointerCell_card_bound q)
  have h := R_blockEncoded_lower (flatMajority q) a ha D payload hpayload B
    (flatHardWeight m) (flatHardWeight_nonnegative m) (flatHardWeight_mass m) β hβ (by
      intro tree ht
      rw [flatHardWeight_score]
      exact hhard tree ht)
  rw [inner_eq_reindex, R_reindex]
  exact h

end QueryComplexity.PointerDistributions

open Filter

namespace QueryComplexity.Construction

open PointerDistributions PointerLowerNumerics

/-- The concrete encoded inner function has the required linear-in-scale
lower bound, obtained from its explicit hard distribution. -/
theorem R_inner_lower_large_scale (s : ℕ) (hs : 1000 ≤ s) :
    (pointerPayloadWidth (arity s) : ℝ) * (arity s : ℝ) ^ 2 * (s : ℝ) / 1000000 ≤
      (R (inner (arity s)) : ℝ) := by
  have hodd : Odd (arity s) := by
    have hp : Even (2 ^ s) := (show Even (2 : ℕ) by decide).pow_of_ne_zero (by omega)
    apply (Nat.odd_sub' (Nat.one_le_pow _ _ (by omega))).mpr
    simpa using hp
  obtain ⟨m, hm⟩ := hodd
  have hq : arity s = 2 * m + 1 := by omega
  have hcell := R_inner_lower_of_cell_bound m (cellBudget s) (3 / 5) (by norm_num) (by
    intro tree ht
    exact pointer_majority_cell_hard s m hs hq tree ht)
  rw [← hq] at hcell
  exact (encoding_budget_lower s (pointerPayloadWidth (arity s))).trans (by exact_mod_cast hcell)

/-- The eventual inner lower bound consumed by the final comparison theorem. -/
theorem eventually_R_G_lower : ∀ᶠ n in atTop,
    (pointerPayloadWidth (pointerArity n) : ℝ) * (pointerArity n : ℝ) ^ 2 *
      (scale n : ℝ) / 1000000 ≤ (R (G n) : ℝ) := by
  filter_upwards [eventually_scale_ge 1000] with n hn
  have h := R_inner_lower_large_scale (scale n) hn
  rw [G, R_toFin]
  simpa only [arity, pointerArity] using h

end QueryComplexity.Construction
