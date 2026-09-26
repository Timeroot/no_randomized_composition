import QueryComplexity.OracleTrees
import QueryComplexity.ProductKernels

open scoped BigOperators

namespace QueryComplexity.OracleOptimization

open FiniteProbability ProductKernels

variable {T A : Type*} [Fintype T] [DecidableEq T] [Fintype A] [DecidableEq A]

def score (f : (T → A) → Bool) (μ : Weight (T → A)) (tree : OracleTree T A Bool) : ℝ :=
  ∑ x, if tree.eval x = f x then μ x else 0

theorem score_leaf (f : (T → A) → Bool) (μ : Weight (T → A)) (b : Bool) :
    score f μ (.leaf b) = labelMass f μ b := by
  simp only [score, OracleTree.eval, labelMass, mass, restrict]
  apply Finset.sum_congr rfl
  intro x _
  simp only [eq_comm]

theorem score_query (f : (T → A) → Bool) (μ : Weight (T → A))
    (t : T) (next : A → OracleTree T A Bool) :
    score f μ (.query t next) = ∑ a, score f (restrictSymbol μ t a) (next a) := by
  simp only [score]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [OracleTree.eval, restrictSymbol]
  rw [Finset.sum_eq_single (x t)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

noncomputable def opt (f : (T → A) → Bool) : ℕ → Weight (T → A) → ℝ
  | 0, μ => max (labelMass f μ false) (labelMass f μ true)
  | B + 1, μ => maxValue (fun o : Option T => match o with
      | none => max (labelMass f μ false) (labelMass f μ true)
      | some t => ∑ a, opt f B (restrictSymbol μ t a))

theorem labelMass_le_opt (f : (T → A) → Bool) (B : ℕ) (μ : Weight (T → A)) (b : Bool) :
    labelMass f μ b ≤ opt f B μ := by
  cases B with
  | zero => cases b <;> first | exact le_max_left _ _ | exact le_max_right _ _
  | succ B =>
    apply le_trans _ (le_maxValue _ (none : Option T))
    cases b <;> first | exact le_max_left _ _ | exact le_max_right _ _

theorem opt_query_le (f : (T → A) → Bool) (B : ℕ) (μ : Weight (T → A)) (t : T) :
    (∑ a, opt f B (restrictSymbol μ t a)) ≤ opt f (B + 1) μ := by
  exact le_maxValue (fun o : Option T => match o with
    | none => max (labelMass f μ false) (labelMass f μ true)
    | some j => ∑ a, opt f B (restrictSymbol μ j a)) (some t)

theorem opt_nonnegative (f : (T → A) → Bool) (B : ℕ) {μ : Weight (T → A)}
    (hμ : Nonnegative μ) : 0 ≤ opt f B μ :=
  (labelMass_nonnegative f hμ false).trans (labelMass_le_opt f B μ false)

theorem exists_optimal_tree (f : (T → A) → Bool) (B : ℕ) (μ : Weight (T → A)) :
    ∃ tree : OracleTree T A Bool, tree.depth ≤ B ∧ score f μ tree = opt f B μ := by
  induction B generalizing μ with
  | zero =>
    by_cases h : labelMass f μ false ≤ labelMass f μ true
    · exact ⟨.leaf true, by simp [OracleTree.depth], by simp [score_leaf, opt, max_eq_right h]⟩
    · exact ⟨.leaf false, by simp [OracleTree.depth],
        by simp [score_leaf, opt, max_eq_left (le_of_not_ge h)]⟩
  | succ B ih =>
    obtain ⟨o, ho⟩ := exists_eq_maxValue (fun o : Option T => match o with
      | none => max (labelMass f μ false) (labelMass f μ true)
      | some t => ∑ a, opt f B (restrictSymbol μ t a))
    cases o with
    | none =>
      by_cases h : labelMass f μ false ≤ labelMass f μ true
      · refine ⟨.leaf true, by simp [OracleTree.depth], ?_⟩
        simpa only [score_leaf, max_eq_right h, opt] using ho
      · refine ⟨.leaf false, by simp [OracleTree.depth], ?_⟩
        simpa only [score_leaf, max_eq_left (le_of_not_ge h), opt] using ho
    | some t =>
      choose next hdepth hscore using fun a => ih (restrictSymbol μ t a)
      refine ⟨.query t next, ?_, ?_⟩
      · simp only [OracleTree.depth]
        have hs : Finset.univ.sup (fun a => (next a).depth) ≤ B :=
          Finset.sup_le fun a _ => hdepth a
        omega
      · rw [score_query]
        simp only [hscore]
        exact ho

theorem opt_le_of_tree_bound (f : (T → A) → Bool) (B : ℕ) (μ : Weight (T → A)) (β : ℝ)
    (h : ∀ tree : OracleTree T A Bool, tree.depth ≤ B → score f μ tree ≤ β) :
    opt f B μ ≤ β := by
  obtain ⟨tree, ht, he⟩ := exists_optimal_tree f B μ
  rw [← he]
  exact h tree ht

theorem score_le_opt (f : (T → A) → Bool) (B : ℕ) (μ : Weight (T → A))
    (tree : OracleTree T A Bool) (hdepth : tree.depth ≤ B) : score f μ tree ≤ opt f B μ := by
  induction B generalizing μ tree with
  | zero =>
    cases tree with
    | leaf b => rw [score_leaf]; exact labelMass_le_opt f 0 μ b
    | query t next => simp [OracleTree.depth] at hdepth
  | succ B ih =>
    cases tree with
    | leaf b => rw [score_leaf]; exact labelMass_le_opt f (B + 1) μ b
    | query t next =>
      rw [score_query]
      apply le_trans _ (opt_query_le f B μ t)
      apply Finset.sum_le_sum
      intro a _
      apply ih
      have ha := Finset.le_sup (f := fun a => (next a).depth) (Finset.mem_univ a)
      dsimp only at ha
      simp only [OracleTree.depth] at hdepth
      omega

theorem opt_mono (f : (T → A) → Bool) (μ : Weight (T → A)) {B C : ℕ} (h : B ≤ C) :
    opt f B μ ≤ opt f C μ := by
  obtain ⟨tree, ht, he⟩ := exists_optimal_tree f B μ
  rw [← he]
  exact score_le_opt f C μ tree (ht.trans h)

end QueryComplexity.OracleOptimization
