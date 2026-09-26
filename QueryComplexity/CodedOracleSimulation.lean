import QueryComplexity.PrivateStates
import QueryComplexity.OracleOptimization

open scoped BigOperators

namespace QueryComplexity.CodedOracleSimulation

open FiniteProbability ProductKernels PrivateKernels QueryCredits

variable {T A J : Type*} [Fintype T] [DecidableEq T] [Fintype A] [DecidableEq A]
  [Fintype J] [DecidableEq J]

/-- Queries to an unopened cell spend one credit.  On the next query after
`d` credits, its entire symbol is revealed and those credits are discharged.
This proof works with repeated bit queries as well as distinct ones. -/
theorem simulate_bound (f : (T → A) → Bool) (d : ℕ)
    (tree : DecisionTree (T × J) Bool) (B : ℕ) (μ : Weight (T → A))
    (K : Kernel T A J) (opened : Finset T) (spent : T → ℕ) (known : T → A)
    (hμ : Nonnegative μ) (hK : Normalized K) (hsupport : KnownSupport opened known μ)
    (hprivate : PrivateState d opened spent K)
    (hspent : ∀ t, t ∉ opened → spent t ≤ d)
    (hbudget : tree.depth + credit opened spent < (B + 1) * (d + 1)) :
    ProductKernels.score f μ K tree ≤ OracleOptimization.opt f B μ := by
  induction tree generalizing B μ K opened spent known with
  | leaf b =>
    rw [ProductKernels.score_leaf f μ hK]
    exact OracleOptimization.labelMass_le_opt f B μ b
  | node coordinate zero one ihz iho =>
    obtain ⟨t, j⟩ := coordinate
    have ih (b : Bool) (B' : ℕ) (μ' : Weight (T → A)) (K' : Kernel T A J)
        (opened' : Finset T) (spent' : T → ℕ) (known' : T → A)
        (hμ' : Nonnegative μ') (hK' : Normalized K')
        (hs' : KnownSupport opened' known' μ') (hp' : PrivateState d opened' spent' K')
        (hc' : ∀ u, u ∉ opened' → spent' u ≤ d)
        (hb' : (if b then one else zero).depth + credit opened' spent' <
          (B' + 1) * (d + 1)) :
        ProductKernels.score f μ' K' (if b then one else zero) ≤
          OracleOptimization.opt f B' μ' := by
      cases b
      · exact ihz B' μ' K' opened' spent' known' hμ' hK' hs' hp' hc' hb'
      · exact iho B' μ' K' opened' spent' known' hμ' hK' hs' hp' hc' hb'
    have hdepth (b : Bool) : (if b then one else zero).depth + 1 ≤
        (DecisionTree.node (t, j) zero one).depth := by
      cases b <;> simp only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte, DecisionTree.depth] <;> omega
    by_cases hopen : t ∈ opened
    · apply score_node_le f μ hK t j zero one (known t) (OracleOptimization.opt f B μ)
      · intro s hs b
        rw [hsupport s hs t hopen]
      · intro b _
        apply ih b B μ _ opened spent known hμ (conditioned_normalized hK t j b) hsupport
          (privateState_conditioned_open hprivate t hopen j b) hspent
        have := hdepth b
        omega
    · by_cases hcheap : spent t < d
      · have he : d - spent t = (d - (spent t + 1)) + 1 := by omega
        have hp := hprivate t hopen
        rw [he] at hp
        apply score_node_le f μ hK t j zero one (known t) (OracleOptimization.opt f B μ)
        · intro s _ b
          exact private_probability hp (s t) (known t) j b
        · intro b hb
          apply ih b B μ _ opened (Function.update spent t (spent t + 1)) known hμ
            (conditioned_normalized hK t j b) hsupport
            (privateState_conditioned_cheap hprivate t hopen hcheap j b (known t) hb)
          · intro u hu
            by_cases hut : u = t
            · subst u; simp only [Function.update_self]; omega
            · simpa only [Function.update_of_ne hut] using hspent u hu
          · rw [credit_increment opened spent t hopen]
            have := hdepth b
            omega
      · have hfull : spent t = d := by have := hspent t hopen; omega
        have hcredit := credit_open opened spent t hopen
        have hpositive : 0 < B := by
          have hc := spent_le_credit opened spent t hopen
          have hd := hdepth false
          by_contra hz
          have hB : B = 0 := by omega
          simp only [hB, zero_add, one_mul] at hbudget
          omega
        obtain ⟨B', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpositive)
        rw [score_split f μ K (.node (t, j) zero one) t]
        apply le_trans (Finset.sum_le_sum fun a _ => ?_) (OracleOptimization.opt_query_le f B' μ t)
        apply score_node_le f (restrictSymbol μ t a) hK t j zero one a
          (OracleOptimization.opt f B' (restrictSymbol μ t a))
        · intro s hs b
          have hst : s t = a := by
            by_contra h
            exact hs (by simp [restrictSymbol, h])
          rw [hst]
        · intro b _
          apply ih b B' (restrictSymbol μ t a) _ (insert t opened) spent (Function.update known t a)
            (restrictSymbol_nonneg hμ t a) (conditioned_normalized hK t j b)
            (knownSupport_restrict hsupport t hopen a)
            (privateState_conditioned_open (privateState_open hprivate t) t (by simp) j b)
          · intro u hu
            exact hspent u (fun h => hu (Finset.mem_insert_of_mem h))
          · have hd := hdepth b
            rw [hfull] at hcredit
            simp only [Nat.succ_eq_add_one] at hbudget
            nlinarith

/-- A private block encoding multiplies the deterministic distributional
query lower bound by its privacy threshold plus one. -/
theorem private_encoding_bound [Nonempty A] (f : (T → A) → Bool) (d B : ℕ)
    (μ : Weight (T → A)) (hμ : Nonnegative μ) (K : Kernel T A J)
    (hK : Normalized K) (hp : ∀ t, Private d (K t))
    (tree : DecisionTree (T × J) Bool) (ht : tree.depth < (B + 1) * (d + 1)) :
    ProductKernels.score f μ K tree ≤ OracleOptimization.opt f B μ := by
  classical
  apply simulate_bound f d tree B μ K ∅ (fun _ => 0) (fun _ => Classical.choice ‹Nonempty A›)
    hμ hK
  · intro s hs t ht; simpa using ht
  · intro t _; simpa using hp t
  · intro t _; exact Nat.zero_le d
  · simpa [credit_empty_zero] using ht

end QueryComplexity.CodedOracleSimulation
