import QueryComplexity.CodedOracleSimulation
import QueryComplexity.Basic

open scoped BigOperators

namespace QueryComplexity.CodedOracleSimulation

open FiniteProbability ProductKernels PrivateKernels AdaptivePrivacy

variable {T A J Seed : Type*} [Fintype T] [DecidableEq T] [Fintype A] [DecidableEq A]
  [Fintype J] [DecidableEq J] [Fintype Seed]

theorem weighted_score_eq (f : (T → A) → Bool) (μ : Weight (T → A))
    (K : Kernel T A J) (tree : Seed → DecisionTree (T × J) Bool) (w : Seed → ℝ) :
    (∑ r, w r * ProductKernels.score f μ K (tree r)) =
      ∑ s, μ s * ∑ x, productWeight K s x *
        ∑ r, if (tree r).eval (fun p => x p.1 p.2) = f s then w r else 0 := by
  simp only [ProductKernels.score, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> ring

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
        apply Finset.sum_le_sum
        intro x _
        by_cases hz : productWeight K s x = 0
        · simp [hz]
        · apply mul_le_mul_of_nonneg_left
          · rw [← hsupport s x hz]
            exact hcorrect _
          · exact Finset.prod_nonneg fun t _ => (hK t (s t)).1 (x t)
  calc
    (2 : ℝ) / 3 = (∑ s, μ s) * (2 / 3) := by change _ = mass μ * _; rw [hmass]; ring
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
    change D (BinaryCode.privateDecoder a ha (x t)) = s t
    rw [he t, hpayload]
  · exact hβ
  · exact hhard

end QueryComplexity.CodedOracleSimulation
