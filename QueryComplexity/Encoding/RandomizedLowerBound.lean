import QueryComplexity.Encoding.ProductKernels
import QueryComplexity.LowerBounds.OracleOptimization
import QueryComplexity.Basic

/-! Lazy revelation of encoded cells and transfer of randomized query lower bounds. -/

open scoped BigOperators

namespace QueryComplexity.QueryCredits

variable {T : Type*} [Fintype T] [DecidableEq T]

def credit (opened : Finset T) (spent : T → ℕ) : ℕ :=
  ∑ t, if t ∈ opened then 0 else spent t

theorem credit_empty_zero : credit (∅ : Finset T) (fun _ => 0) = 0 := by simp [credit]

theorem credit_increment (opened : Finset T) (spent : T → ℕ) (t : T) (ht : t ∉ opened) :
    credit opened (Function.update spent t (spent t + 1)) = credit opened spent + 1 := by
  have he (u : T) : (if u ∈ opened then 0 else Function.update spent t (spent t + 1) u) =
      (if u ∈ opened then 0 else spent u) + (if u = t then 1 else 0) := by
    by_cases hu : u = t
    · subst u; simp [ht]
    · simp [hu]
  simp only [credit, he, Finset.sum_add_distrib]
  simp

theorem credit_open (opened : Finset T) (spent : T → ℕ) (t : T) (ht : t ∉ opened) :
    credit (insert t opened) spent + spent t = credit opened spent := by
  have he (u : T) : (if u ∈ opened then 0 else spent u) =
      (if u ∈ insert t opened then 0 else spent u) + (if u = t then spent t else 0) := by
    by_cases hu : u = t
    · subst u; simp [ht]
    · simp [hu]
  conv_rhs => unfold credit
  simp only [he, Finset.sum_add_distrib]
  simp [credit]

theorem spent_le_credit (opened : Finset T) (spent : T → ℕ) (t : T) (ht : t ∉ opened) :
    spent t ≤ credit opened spent := by
  have h := credit_open opened spent t ht
  omega

end QueryComplexity.QueryCredits

namespace QueryComplexity.CodedOracleSimulation

open FiniteProbability ProductKernels PrivateKernels QueryCredits

variable {T A J : Type*} [Fintype T] [DecidableEq T] [Fintype A] [DecidableEq A]
  [Fintype J] [DecidableEq J]

def PrivateState (d : ℕ) (opened : Finset T) (spent : T → ℕ) (K : Kernel T A J) : Prop :=
  ∀ t, t ∉ opened → Private (d - spent t) (K t)

def KnownSupport (opened : Finset T) (known : T → A) (μ : Weight (T → A)) : Prop :=
  ∀ s, μ s ≠ 0 → ∀ t ∈ opened, s t = known t

omit [Fintype T] [Fintype A] [DecidableEq A] in
theorem privateState_conditioned_open {d : ℕ} {opened : Finset T} {spent : T → ℕ}
    {K : Kernel T A J} (hK : PrivateState d opened spent K)
    (t : T) (ht : t ∈ opened) (j : J) (b : Bool) :
    PrivateState d opened spent (conditioned K t j b) := by
  intro u hu
  have hut : u ≠ t := by intro h; subst u; exact hu ht
  simpa only [conditioned, Function.update_of_ne hut] using hK u hu

omit [Fintype T] [Fintype A] [DecidableEq A] in
theorem privateState_conditioned_cheap {d : ℕ} {opened : Finset T} {spent : T → ℕ}
    {K : Kernel T A J} (hK : PrivateState d opened spent K)
    (t : T) (ht : t ∉ opened) (hc : spent t < d) (j : J) (b : Bool) (a₀ : A)
    (hp : probability (K t a₀) j b ≠ 0) :
    PrivateState d opened (Function.update spent t (spent t + 1)) (conditioned K t j b) := by
  intro u hu
  by_cases hut : u = t
  · subst u
    have he : d - spent t = (d - (spent t + 1)) + 1 := by omega
    have hk := hK t ht
    rw [he] at hk
    simpa only [Function.update_self, conditioned] using private_conditional hk j b a₀ hp
  · simpa only [Function.update_of_ne hut, conditioned] using hK u hu

omit [Fintype T] [Fintype A] [DecidableEq A] in
theorem privateState_open {d : ℕ} {opened : Finset T} {spent : T → ℕ}
    {K : Kernel T A J} (hK : PrivateState d opened spent K) (t : T) :
    PrivateState d (insert t opened) spent K := by
  intro u hu
  exact hK u (fun h => hu (Finset.mem_insert_of_mem h))

omit [Fintype T] [Fintype A] in
theorem knownSupport_restrict {opened : Finset T} {known : T → A} {μ : Weight (T → A)}
    (hμ : KnownSupport opened known μ) (t : T) (ht : t ∉ opened) (a : A) :
    KnownSupport (insert t opened) (Function.update known t a) (restrictSymbol μ t a) := by
  intro s hs u hu
  have hst : s t = a := by
    by_contra h
    exact hs (by simp [restrictSymbol, h])
  have hms : μ s ≠ 0 := by simpa [restrictSymbol, hst] using hs
  rcases Finset.mem_insert.mp hu with hut | huo
  · subst u; simp [hst]
  · have hut : u ≠ t := by intro h; subst u; exact ht huo
    simpa [Function.update_of_ne hut] using hμ s hms u huo

end QueryComplexity.CodedOracleSimulation

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
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, DecisionTree.depth] <;> omega
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
  · intro s hs t ht; simp at ht
  · intro t _; simpa using hp t
  · intro t _; exact Nat.zero_le d
  · simpa [credit_empty_zero] using ht

end QueryComplexity.CodedOracleSimulation

open scoped BigOperators

namespace QueryComplexity.CodedOracleSimulation

open FiniteProbability ProductKernels PrivateKernels AdaptivePrivacy

variable {T A J Seed : Type*} [Fintype T] [DecidableEq T] [Fintype A] [DecidableEq A]
  [Fintype J] [DecidableEq J] [Fintype Seed]

omit [DecidableEq A] in
theorem weighted_score_eq (f : (T → A) → Bool) (μ : Weight (T → A))
    (K : Kernel T A J) (tree : Seed → DecisionTree (T × J) Bool) (w : Seed → ℝ) :
    (∑ r, w r * ProductKernels.score f μ K (tree r)) =
      ∑ s, μ s * ∑ x, productWeight K s x *
        ∑ r, if (tree r).eval (fun p => x p.1 p.2) = f s then w r else 0 := by
  simp only [ProductKernels.score, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> ring

omit [DecidableEq A] in
theorem weighted_score_lower (f : (T → A) → Bool) (g : BoolFn (T × J))
    (μ : Weight (T → A)) (hμ : Nonnegative μ) (hmass : mass μ = 1)
    (K : Kernel T A J) (hK : Normalized K)
    (hsupport : ∀ s x, productWeight K s x ≠ 0 → g (fun p => x p.1 p.2) = f s)
    (tree : Seed → DecisionTree (T × J) Bool) (w : Seed → ℝ)
    (hcorrect : ∀ x, (2 : ℝ) / 3 ≤ ∑ r, if (tree r).eval x = g x then w r else 0) :
    (2 : ℝ) / 3 ≤ ∑ r, w r * ProductKernels.score f μ K (tree r) := by
  rw [weighted_score_eq]
  have hp (s : T → A) : (2 : ℝ) / 3 ≤ ∑ x, productWeight K s x *
      ∑ r, if (tree r).eval (fun p => x p.1 p.2) = f s then w r else 0 := by
    calc
      (2 : ℝ) / 3 = (∑ x, productWeight K s x) * (2 / 3) := by rw [productWeight_mass hK]; ring
      _ = ∑ x, productWeight K s x * (2 / 3) := Finset.sum_mul _ _ _
      _ ≤ _ := by
        refine Finset.sum_le_sum fun x _ => ?_
        by_cases hz : productWeight K s x = 0
        · simp [hz]
        · apply mul_le_mul_of_nonneg_left
          · rw [← hsupport s x hz]
            exact hcorrect _
          · exact Finset.prod_nonneg fun t _ => (hK t (s t)).1 (x t)
  calc
    (2 : ℝ) / 3 = (∑ s, μ s) * (2 / 3) := by rw [← mass, hmass, one_mul]
    _ = ∑ s, μ s * (2 / 3) := Finset.sum_mul _ _ _
    _ ≤ _ := Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hp s) (hμ s)

/-- Distributional hardness of full-cell trees transfers to ordinary
worst-case bounded-error randomized bit-query complexity. -/
theorem R_lower_of_private_kernel [Nonempty A]
    (f : (T → A) → Bool) (g : BoolFn (T × J)) (d B : ℕ)
    (μ : Weight (T → A)) (hμ : Nonnegative μ) (hmass : mass μ = 1)
    (K : Kernel T A J) (hK : Normalized K) (hp : ∀ t, Private d (K t))
    (hsupport : ∀ s x, productWeight K s x ≠ 0 → g (fun p => x p.1 p.2) = f s)
    (β : ℝ) (hβ : β < 2 / 3)
    (hhard : ∀ tree : OracleTree T A Bool, tree.depth ≤ B →
      OracleOptimization.score f μ tree ≤ β) :
    (B + 1) * (d + 1) ≤ R g := by
  by_contra hn
  have hR : R g < (B + 1) * (d + 1) := by omega
  obtain ⟨m, tree, w, hdepth, hw, hwone, hcorrect⟩ := hasRandomizedBound_R g
  have hl := weighted_score_lower f g μ hμ hmass K hK hsupport tree w hcorrect
  have hopt := OracleOptimization.opt_le_of_tree_bound f B μ β hhard
  have hu : (∑ r, w r * ProductKernels.score f μ K (tree r)) ≤ β := by
    calc
      _ ≤ ∑ r, w r * β := Finset.sum_le_sum fun r _ =>
        mul_le_mul_of_nonneg_left ((private_encoding_bound f d B μ hμ K hK hp
          (tree r) ((hdepth r).trans_lt hR)).trans hopt) (hw r)
      _ = β := by rw [← Finset.sum_mul, hwone, one_mul]
  linarith

noncomputable def blockEncoded (f : (T → A) → Bool) (decode : (J → Bool) → A) : BoolFn (T × J) :=
  fun x => f (fun t => decode (fun j => x (t, j)))

/-- Uniform cosets of the explicit private binary code provide the kernels
needed above, for any finite output alphabet. -/
theorem R_blockEncoded_lower [Nonempty A]
    (f : (T → A) → Bool) (a : ℕ) (ha : 0 < a)
    (D : (Fin a → Bool) → A) (payload : A → Fin a → Bool)
    (hpayload : ∀ s, D (payload s) = s) (B : ℕ)
    (μ : Weight (T → A)) (hμ : Nonnegative μ) (hmass : mass μ = 1)
    (β : ℝ) (hβ : β < 2 / 3)
    (hhard : ∀ tree : OracleTree T A Bool, tree.depth ≤ B →
      OracleOptimization.score f μ tree ≤ β) :
    (B + 1) * (12 * a + 1) ≤
      R (blockEncoded f (fun x => D (BinaryCode.privateDecoder a ha x))) := by
  let K : Kernel T A (Fin (36 * a)) :=
    fun _ s => fiberWeight (BinaryCode.privateDecoder a ha) (payload s)
  apply R_lower_of_private_kernel f _ (12 * a) B μ hμ hmass K
  · intro t s
    exact ⟨fiberWeight_nonnegative _ _, mass_fiberWeight _ (BinaryCode.privateDecoder_surjective a ha) _⟩
  · intro t
    exact private_fiber a ha payload
  · intro s x hx
    have he (t : T) : BinaryCode.privateDecoder a ha (x t) = payload (s t) := by
      have ht : K t (s t) (x t) ≠ 0 :=
        (Finset.prod_ne_zero_iff.mp hx) t (Finset.mem_univ t)
      by_contra hn
      apply ht
      simp [K, fiberWeight, hn]
    unfold blockEncoded
    congr 1
    funext t
    simp only [he t, hpayload]
  · exact hβ
  · exact hhard

end QueryComplexity.CodedOracleSimulation
