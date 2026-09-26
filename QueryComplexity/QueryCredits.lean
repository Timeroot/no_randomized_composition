import QueryComplexity.ProductKernels

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
    · simp [Function.update_of_ne hu, hu]
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
