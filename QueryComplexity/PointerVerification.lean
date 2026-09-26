import QueryComplexity.Pointer

namespace QueryComplexity.Pointer

def canonicalLinks {q : ℕ} (x : PointerInput q) (i j : Fin q) : Fin q → Fin q :=
  fun c => ((x i j).row c).getD i

theorem canonicalLinks_eq {q : ℕ} {x : PointerInput q} {i j : Fin q}
    {linked : Fin q → Fin q} (h : Valid x i j linked) (c : Fin q) (hc : c ≠ j) :
    canonicalLinks x i j c = linked c := by
  simp [canonicalLinks, (h.2.2.1 c hc).1]

theorem valid_change_links {q : ℕ} {x : PointerInput q} {i j : Fin q}
    {linked linked' : Fin q → Fin q} (h : Valid x i j linked)
    (heq : ∀ c, c ≠ j → linked' c = linked c) : Valid x i j linked' := by
  classical
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · intro c hc
    rw [heq c hc]
    exact h.2.2.1 c hc
  · have hf : Finset.univ.filter (fun c => c ≠ j ∧ good x i j (linked' c) c) =
        Finset.univ.filter (fun c => c ≠ j ∧ good x i j (linked c) c) := by
      ext c
      by_cases hc : c = j
      · simp [hc]
      · simp [hc, heq c hc]
    rw [hf]
    exact h.2.2.2

theorem exists_valid_iff_canonical {q : ℕ} (x : PointerInput q) (i j : Fin q) :
    (∃ linked, Valid x i j linked) ↔ Valid x i j (canonicalLinks x i j) := by
  constructor
  · rintro ⟨linked, h⟩
    exact valid_change_links h (canonicalLinks_eq h)
  · exact fun h => ⟨_, h⟩

/-- Verifying a fixed candidate requires only its column and linked cells. -/
theorem valid_of_agree {q : ℕ} {x y : PointerInput q} {i j : Fin q}
    {linked : Fin q → Fin q} (h : Valid x i j linked)
    (hcolumn : ∀ r, x r j = y r j)
    (hlinked : ∀ c, c ≠ j → x (linked c) c = y (linked c) c) :
    Valid y i j linked := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r
    rw [← hcolumn r]
    exact h.1 r
  · intro r hr c hc
    rw [← hcolumn r]
    exact h.2.1 r hr c hc
  · intro c hc
    rw [← hcolumn i, ← hlinked c hc]
    exact h.2.2.1 c hc
  · have hf : Finset.univ.filter (fun c => c ≠ j ∧ good y i j (linked c) c) =
        Finset.univ.filter (fun c => c ≠ j ∧ good x i j (linked c) c) := by
      ext c
      by_cases hc : c = j
      · simp [hc]
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, good]
        rw [← hlinked c hc]
    rw [hf]
    exact h.2.2.2

theorem valid_iff_of_agree {q : ℕ} {x y : PointerInput q} {i j : Fin q}
    {linked : Fin q → Fin q}
    (hcolumn : ∀ r, x r j = y r j)
    (hlinked : ∀ c, c ≠ j → x (linked c) c = y (linked c) c) :
    Valid x i j linked ↔ Valid y i j linked :=
  ⟨fun h => valid_of_agree h hcolumn hlinked,
    fun h => valid_of_agree h (fun r => (hcolumn r).symm) (fun c hc => (hlinked c hc).symm)⟩

theorem canonicalLinks_eq_of_agree_column {q : ℕ} {x y : PointerInput q} {i j : Fin q}
    (hcolumn : ∀ r, x r j = y r j) : canonicalLinks x i j = canonicalLinks y i j := by
  unfold canonicalLinks
  rw [hcolumn i]

end QueryComplexity.Pointer
