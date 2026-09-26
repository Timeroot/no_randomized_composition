import QueryComplexity.AdaptivePrivacy

open scoped BigOperators

namespace QueryComplexity.PrivateKernels

open FiniteProbability DirectProduct AdaptivePrivacy

variable {J A : Type*} [Fintype J] [DecidableEq J]

def Private (r : ℕ) (K : A → Weight (J → Bool)) : Prop :=
  ∀ a b trace, trace.length ≤ r → mass (traceWeight (K a) trace) =
    mass (traceWeight (K b) trace)

def probability (K : Weight (J → Bool)) (j : J) (b : Bool) : ℝ :=
  mass (queried K j b)

noncomputable def conditional (K : Weight (J → Bool)) (j : J) (b : Bool) :
    Weight (J → Bool) :=
  if probability K j b = 0 then K else fun x => queried K j b x / probability K j b

theorem probability_nonneg {K : Weight (J → Bool)} (hK : Nonnegative K) (j : J) (b : Bool) :
    0 ≤ probability K j b := mass_nonnegative (queried_nonnegative hK j b)

theorem probability_add (K : Weight (J → Bool)) (j : J) :
    probability K j false + probability K j true = mass K := mass_restrict_add K _

theorem conditional_nonneg {K : Weight (J → Bool)} (hK : Nonnegative K) (j : J) (b : Bool) :
    Nonnegative (conditional K j b) := by
  intro x
  unfold conditional
  split_ifs
  · exact hK x
  · exact div_nonneg (queried_nonnegative hK j b x) (probability_nonneg hK j b)

theorem conditional_mass {K : Weight (J → Bool)} (hK : mass K = 1) (j : J) (b : Bool) :
    mass (conditional K j b) = 1 := by
  unfold conditional
  split_ifs with h
  · exact hK
  · simp only [mass, ← Finset.sum_div]
    exact div_self h

theorem conditional_factor {K : Weight (J → Bool)} (hK : Nonnegative K)
    (j : J) (b : Bool) (x : J → Bool) :
    probability K j b * conditional K j b x = queried K j b x := by
  by_cases hp : probability K j b = 0
  · have hx : queried K j b x = 0 := by
      have hle : queried K j b x ≤ probability K j b :=
        Finset.single_le_sum (fun y _ => queried_nonnegative hK j b y) (Finset.mem_univ x)
      exact le_antisymm (hle.trans_eq hp) (queried_nonnegative hK j b x)
    simp [hp, hx]
  · simp only [conditional, hp, if_false]
    field_simp

theorem traceWeight_div (K : Weight (J → Bool)) (trace : List (J × Bool)) (c : ℝ) :
    traceWeight (fun x => K x / c) trace = fun x => traceWeight K trace x / c := by
  funext x
  simp only [traceWeight_apply]
  split_ifs <;> simp

theorem conditional_trace_mass (K : Weight (J → Bool)) (j : J) (b : Bool)
    (hp : probability K j b ≠ 0) (trace : List (J × Bool)) :
    mass (traceWeight (conditional K j b) trace) =
      mass (traceWeight K ((j, b) :: trace)) / probability K j b := by
  simp only [conditional, hp, if_false, traceWeight_div, mass, ← Finset.sum_div, traceWeight]

theorem private_probability {K : A → Weight (J → Bool)} {r : ℕ}
    (hK : Private (r + 1) K) (a b : A) (j : J) (v : Bool) :
    probability (K a) j v = probability (K b) j v := by
  simpa only [traceWeight, probability] using hK a b [(j, v)] (by simp)

theorem private_conditional {K : A → Weight (J → Bool)} {r : ℕ}
    (hK : Private (r + 1) K) (j : J) (v : Bool) (a₀ : A)
    (hp : probability (K a₀) j v ≠ 0) :
    Private r (fun a => conditional (K a) j v) := by
  intro a b trace ht
  have ha := private_probability hK a a₀ j v
  have hb := private_probability hK b a₀ j v
  rw [conditional_trace_mass _ _ _ (by rwa [ha]),
    conditional_trace_mass _ _ _ (by rwa [hb]), ha, hb]
  rw [hK a b ((j, v) :: trace) (by simp; omega)]

theorem private_mono {K : A → Weight (J → Bool)} {r s : ℕ}
    (hK : Private r K) (hs : s ≤ r) : Private s K :=
  fun a b trace ht => hK a b trace (ht.trans hs)

theorem private_fiber (a : ℕ) (ha : 0 < a) (payload : A → Fin a → Bool) :
    Private (12 * a) (fun s => fiberWeight (BinaryCode.privateDecoder a ha) (payload s)) :=
  fun s t trace ht => privateDecoder_trace_masses a ha (payload s) (payload t) trace ht

end QueryComplexity.PrivateKernels
