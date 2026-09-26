import QueryComplexity.QueryCredits

namespace QueryComplexity.CodedOracleSimulation

open FiniteProbability ProductKernels PrivateKernels QueryCredits

variable {T A J : Type*} [Fintype T] [DecidableEq T] [Fintype A] [DecidableEq A]
  [Fintype J] [DecidableEq J]

def PrivateState (d : ℕ) (opened : Finset T) (spent : T → ℕ) (K : Kernel T A J) : Prop :=
  ∀ t, t ∉ opened → Private (d - spent t) (K t)

def KnownSupport (opened : Finset T) (known : T → A) (μ : Weight (T → A)) : Prop :=
  ∀ s, μ s ≠ 0 → ∀ t ∈ opened, s t = known t

theorem privateState_conditioned_open {d : ℕ} {opened : Finset T} {spent : T → ℕ}
    {K : Kernel T A J} (hK : PrivateState d opened spent K)
    (t : T) (ht : t ∈ opened) (j : J) (b : Bool) :
    PrivateState d opened spent (conditioned K t j b) := by
  intro u hu
  have hut : u ≠ t := by intro h; subst u; exact hu ht
  simpa only [conditioned, Function.update_of_ne hut] using hK u hu

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

theorem privateState_open {d : ℕ} {opened : Finset T} {spent : T → ℕ}
    {K : Kernel T A J} (hK : PrivateState d opened spent K) (t : T) :
    PrivateState d (insert t opened) spent K := by
  intro u hu
  exact hK u (fun h => hu (Finset.mem_insert_of_mem h))

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
