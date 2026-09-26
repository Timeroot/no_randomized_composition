import QueryComplexity.FiniteProbability
import QueryComplexity.Reindex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic

/-! Finite weighted decision-tree bounds for direct products. -/

open scoped BigOperators

namespace QueryComplexity
namespace DirectProduct

open FiniteProbability

universe u

variable {T : Type u} [Fintype T] [DecidableEq T]

abbrev Input (T : Type u) := T → Bool

def score (f : BoolFn T) (ν : Weight (Input T)) (tree : DecisionTree T Bool) : ℝ :=
  ∑ x, if tree.eval x = f x then ν x else 0

def queried (ν : Weight (Input T)) (j : T) (b : Bool) : Weight (Input T) :=
  restrict ν (fun x => x j) b

omit [Fintype T] [DecidableEq T] in
theorem queried_nonnegative {ν : Weight (Input T)} (hν : Nonnegative ν)
    (j : T) (b : Bool) : Nonnegative (queried ν j b) :=
  restrict_nonnegative hν _ _

theorem score_leaf (f : BoolFn T) (ν : Weight (Input T)) (b : Bool) :
    score f ν (.leaf b) = labelMass f ν b := by
  simp only [score, DecisionTree.eval, labelMass, mass, restrict]
  apply Finset.sum_congr rfl
  intro x _
  simp only [eq_comm]

theorem score_node (f : BoolFn T) (ν : Weight (Input T)) (j : T)
    (zero one : DecisionTree T Bool) :
    score f ν (.node j zero one) =
      score f (queried ν j false) zero + score f (queried ν j true) one := by
  simp only [score, DecisionTree.eval, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : x j = true
  · simp [queried, restrict, h]
  · have hfalse : x j = false := Bool.eq_false_of_not_eq_true h
    simp [queried, restrict, hfalse]

noncomputable def opt (f : BoolFn T) : ℕ → Weight (Input T) → ℝ
  | 0, ν => max (labelMass f ν false) (labelMass f ν true)
  | t + 1, ν => maxValue (fun o : Option T => match o with
      | none => max (labelMass f ν false) (labelMass f ν true)
      | some j => opt f t (queried ν j false) + opt f t (queried ν j true))

theorem labelMass_le_opt (f : BoolFn T) (t : ℕ) (ν : Weight (Input T)) (b : Bool) :
    labelMass f ν b ≤ opt f t ν := by
  cases t with
  | zero =>
    cases b
    · exact le_max_left _ _
    · exact le_max_right _ _
  | succ t =>
    apply le_trans _ (le_maxValue _ (none : Option T))
    cases b
    · exact le_max_left _ _
    · exact le_max_right _ _

theorem opt_query_le (f : BoolFn T) (t : ℕ) (ν : Weight (Input T)) (j : T) :
    opt f t (queried ν j false) + opt f t (queried ν j true) ≤ opt f (t + 1) ν := by
  exact le_maxValue (fun o : Option T => match o with
    | none => max (labelMass f ν false) (labelMass f ν true)
    | some i => opt f t (queried ν i false) + opt f t (queried ν i true)) (some j)

theorem opt_nonnegative (f : BoolFn T) (t : ℕ) {ν : Weight (Input T)}
    (hν : Nonnegative ν) : 0 ≤ opt f t ν :=
  (labelMass_nonnegative f hν false).trans (labelMass_le_opt f t ν false)

theorem half_mass_le_opt (f : BoolFn T) (t : ℕ) (ν : Weight (Input T)) :
    mass ν / 2 ≤ opt f t ν := by
  have h0 := labelMass_le_opt f t ν false
  have h1 := labelMass_le_opt f t ν true
  have hs := labelMass_false_add_true f ν
  linarith

theorem opt_le_mass (f : BoolFn T) (t : ℕ) {ν : Weight (Input T)}
    (hν : Nonnegative ν) : opt f t ν ≤ mass ν := by
  induction t generalizing ν with
  | zero =>
    exact max_le (labelMass_le_mass f hν false) (labelMass_le_mass f hν true)
  | succ t ih =>
    apply maxValue_le
    intro o
    cases o with
    | none => exact max_le (labelMass_le_mass f hν false) (labelMass_le_mass f hν true)
    | some j =>
      calc
        opt f t (queried ν j false) + opt f t (queried ν j true)
            ≤ mass (queried ν j false) + mass (queried ν j true) :=
          add_le_add (ih (queried_nonnegative hν j false))
            (ih (queried_nonnegative hν j true))
        _ = mass ν := mass_restrict_add ν (fun x => x j)

theorem exists_optimal_tree (f : BoolFn T) (t : ℕ) (ν : Weight (Input T)) :
    ∃ tree : DecisionTree T Bool, tree.depth ≤ t ∧ score f ν tree = opt f t ν := by
  induction t generalizing ν with
  | zero =>
    by_cases h : labelMass f ν false ≤ labelMass f ν true
    · exact ⟨.leaf true, by simp [DecisionTree.depth], by simp [score_leaf, opt, max_eq_right h]⟩
    · exact ⟨.leaf false, by simp [DecisionTree.depth],
        by simp [score_leaf, opt, max_eq_left (le_of_not_ge h)]⟩
  | succ t ih =>
    obtain ⟨o, ho⟩ := exists_eq_maxValue (fun o : Option T => match o with
      | none => max (labelMass f ν false) (labelMass f ν true)
      | some j => opt f t (queried ν j false) + opt f t (queried ν j true))
    cases o with
    | none =>
      by_cases h : labelMass f ν false ≤ labelMass f ν true
      · refine ⟨.leaf true, by simp [DecisionTree.depth], ?_⟩
        simpa only [score_leaf, max_eq_right h, opt] using ho
      · refine ⟨.leaf false, by simp [DecisionTree.depth], ?_⟩
        simpa only [score_leaf, max_eq_left (le_of_not_ge h), opt] using ho
    | some j =>
      obtain ⟨zero, hz, hzs⟩ := ih (queried ν j false)
      obtain ⟨one, h1, h1s⟩ := ih (queried ν j true)
      refine ⟨.node j zero one, ?_, ?_⟩
      · simp only [DecisionTree.depth]
        omega
      · rw [score_node, hzs, h1s]
        exact ho

theorem opt_le_of_tree_bound (f : BoolFn T) (t : ℕ) (ν : Weight (Input T)) (β : ℝ)
    (h : ∀ tree : DecisionTree T Bool, tree.depth ≤ t → score f ν tree ≤ β) :
    opt f t ν ≤ β := by
  obtain ⟨tree, ht, he⟩ := exists_optimal_tree f t ν
  rw [← he]
  exact h tree ht

noncomputable def localPotential (f : BoolFn T) (budget spent : ℕ)
    (ν : Weight (Input T)) : ℝ :=
  if spent ≤ budget then opt f (budget - spent) ν else mass ν / 2

theorem localPotential_nonnegative (f : BoolFn T) (budget spent : ℕ)
    {ν : Weight (Input T)} (hν : Nonnegative ν) :
    0 ≤ localPotential f budget spent ν := by
  unfold localPotential
  split_ifs
  · exact opt_nonnegative f _ hν
  · exact div_nonneg (mass_nonnegative hν) (by norm_num)

theorem localPotential_split (f : BoolFn T) (budget spent : ℕ)
    (ν : Weight (Input T)) (j : T) :
    localPotential f budget (spent + 1) (queried ν j false) +
      localPotential f budget (spent + 1) (queried ν j true) ≤
        localPotential f budget spent ν := by
  by_cases hs : spent < budget
  · have hle : spent ≤ budget := Nat.le_of_lt hs
    have hle' : spent + 1 ≤ budget := by omega
    have he : budget - spent = (budget - (spent + 1)) + 1 := by omega
    simp only [localPotential, hle, hle', if_true]
    rw [he]
    exact opt_query_le f _ ν j
  · by_cases he : spent = budget
    · subst spent
      simp only [localPotential, Nat.not_succ_le_self, if_false, le_refl, if_true, Nat.sub_self]
      rw [← add_div, show mass (queried ν j false) + mass (queried ν j true) = mass ν from
        mass_restrict_add ν (fun x => x j)]
      exact half_mass_le_opt f 0 ν
    · have hgt : ¬ spent ≤ budget := by omega
      have hgt' : ¬ spent + 1 ≤ budget := by omega
      simp only [localPotential, hgt, hgt', if_false]
      rw [← add_div, show mass (queried ν j false) + mass (queried ν j true) = mass ν from
        mass_restrict_add ν (fun x => x j)]

theorem labelMass_le_factor_potential (f : BoolFn T) (budget spent : ℕ)
    {ν : Weight (Input T)} (hν : Nonnegative ν) (b : Bool) :
    labelMass f ν b ≤
      (if budget < spent then (2 : ℝ) else 1) * localPotential f budget spent ν := by
  by_cases hs : spent ≤ budget
  · simp only [localPotential, hs, if_true, Nat.not_lt_of_ge hs, if_false, one_mul]
    exact labelMass_le_opt f _ ν b
  · have hgt : budget < spent := by omega
    simp only [localPotential, hs, if_false, hgt, if_true]
    have hm := labelMass_le_mass f hν b
    linarith

section Product

variable {I : Type*} [Fintype I] [DecidableEq I]

def blockUpdate (ν : I → Weight (Input T)) (i : I) (j : T) (b : Bool) :=
  Function.update ν i (queried (ν i) j b)

def spentUpdate (s : I → ℕ) (i : I) := Function.update s i (s i + 1)

omit [Fintype T] [DecidableEq T] [Fintype I] in
theorem blockUpdate_nonnegative {ν : I → Weight (Input T)}
    (hν : ∀ i, Nonnegative (ν i)) (i : I) (j : T) (b : Bool) :
    ∀ k, Nonnegative (blockUpdate ν i j b k) := by
  intro k
  by_cases hk : k = i
  · subst k
    simpa [blockUpdate] using queried_nonnegative (hν i) j b
  · simpa [blockUpdate, hk] using hν k

noncomputable def potential (f : BoolFn T) (budget : ℕ)
    (s : I → ℕ) (ν : I → Weight (Input T)) : ℝ :=
  ∏ i, localPotential f budget (s i) (ν i)

omit [DecidableEq I] in
theorem potential_nonnegative (f : BoolFn T) (budget : ℕ)
    (s : I → ℕ) {ν : I → Weight (Input T)} (hν : ∀ i, Nonnegative (ν i)) :
    0 ≤ potential f budget s ν :=
  Finset.prod_nonneg fun i _ => localPotential_nonnegative f budget (s i) (hν i)

theorem potential_update (f : BoolFn T) (budget : ℕ) (s : I → ℕ)
    (ν : I → Weight (Input T)) (i : I) (j : T) (b : Bool) :
    potential f budget (spentUpdate s i) (blockUpdate ν i j b) =
      localPotential f budget (s i + 1) (queried (ν i) j b) *
        ∏ k ∈ Finset.univ.erase i, localPotential f budget (s k) (ν k) := by
  unfold potential
  have he : (fun k => localPotential f budget (spentUpdate s i k) (blockUpdate ν i j b k)) =
      Function.update (fun k => localPotential f budget (s k) (ν k)) i
        (localPotential f budget (s i + 1) (queried (ν i) j b)) := by
    funext k
    by_cases hk : k = i
    · subst k
      simp [spentUpdate, blockUpdate]
    · simp [spentUpdate, blockUpdate, hk]
  rw [he, Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]

theorem potential_split (f : BoolFn T) (budget : ℕ) (s : I → ℕ)
    {ν : I → Weight (Input T)} (hν : ∀ i, Nonnegative (ν i)) (i : I) (j : T) :
    potential f budget (spentUpdate s i) (blockUpdate ν i j false) +
      potential f budget (spentUpdate s i) (blockUpdate ν i j true) ≤
        potential f budget s ν := by
  rw [potential_update, potential_update, ← add_mul]
  have hn : 0 ≤ ∏ k ∈ Finset.univ.erase i, localPotential f budget (s k) (ν k) :=
    Finset.prod_nonneg fun k _ => localPotential_nonnegative f budget (s k) (hν k)
  calc
    _ ≤ localPotential f budget (s i) (ν i) *
        ∏ k ∈ Finset.univ.erase i, localPotential f budget (s k) (ν k) :=
      mul_le_mul_of_nonneg_right (localPotential_split f budget (s i) (ν i) j) hn
    _ = potential f budget s ν :=
      Finset.mul_prod_erase Finset.univ
        (fun k => localPotential f budget (s k) (ν k)) (Finset.mem_univ i)

def heavyCount (budget : ℕ) (s : I → ℕ) : ℕ :=
  ∑ i, if budget < s i then 1 else 0

omit [DecidableEq I] in
theorem heavyCount_mul_le (budget : ℕ) (s : I → ℕ) :
    heavyCount budget s * (budget + 1) ≤ ∑ i, s i := by
  rw [heavyCount, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : budget < s i
  · simp only [hi, if_true, one_mul]
    omega
  · simp [hi]

omit [DecidableEq I] in
theorem heavyCount_le_div (budget q : ℕ) (s : I → ℕ) (hs : ∑ i, s i ≤ q) :
    heavyCount budget s ≤ q / (budget + 1) := by
  apply (Nat.le_div_iff_mul_le (Nat.succ_pos budget)).2
  exact (heavyCount_mul_le budget s).trans hs

omit [DecidableEq I] in
theorem factor_product (budget : ℕ) (s : I → ℕ) :
    (∏ i, if budget < s i then (2 : ℝ) else 1) = 2 ^ heavyCount budget s := by
  rw [heavyCount, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> norm_num

theorem leafMass_le_potential (f : BoolFn T) (budget q : ℕ)
    (s : I → ℕ) {ν : I → Weight (Input T)} (hν : ∀ i, Nonnegative (ν i))
    (hs : ∑ i, s i ≤ q) (b : I → Bool) :
    (∏ i, labelMass f (ν i) (b i)) ≤
      (2 : ℝ) ^ (q / (budget + 1)) * potential f budget s ν := by
  calc
    _ ≤ ∏ i, (if budget < s i then (2 : ℝ) else 1) *
        localPotential f budget (s i) (ν i) := by
      apply Finset.prod_le_prod
      · intro i _
        exact labelMass_nonnegative f (hν i) (b i)
      · intro i _
        exact labelMass_le_factor_potential f budget (s i) (hν i) (b i)
    _ = (2 : ℝ) ^ heavyCount budget s * potential f budget s ν := by
      rw [Finset.prod_mul_distrib, factor_product]
      rfl
    _ ≤ (2 : ℝ) ^ (q / (budget + 1)) * potential f budget s ν := by
      apply mul_le_mul_of_nonneg_right _ (potential_nonnegative f budget s hν)
      exact pow_le_pow_right₀ (by norm_num) (heavyCount_le_div budget q s hs)

def productScore (f : BoolFn T) :
    DecisionTree (I × T) (I → Bool) → (I → Weight (Input T)) → ℝ
  | .leaf b, ν => ∏ i, labelMass f (ν i) (b i)
  | .node (i, j) zero one, ν =>
      productScore f zero (blockUpdate ν i j false) +
        productScore f one (blockUpdate ν i j true)

theorem sum_spentUpdate (s : I → ℕ) (i : I) :
    (∑ k, spentUpdate s i k) = (∑ k, s k) + 1 := by
  unfold spentUpdate
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.add_sum_erase Finset.univ s (Finset.mem_univ i)
  omega

theorem productScore_le_potential (f : BoolFn T) (budget q : ℕ)
    (tree : DecisionTree (I × T) (I → Bool))
    (s : I → ℕ) (ν : I → Weight (Input T))
    (hν : ∀ i, Nonnegative (ν i))
    (hs : (∑ i, s i) + tree.depth ≤ q) :
    productScore f tree ν ≤ (2 : ℝ) ^ (q / (budget + 1)) * potential f budget s ν := by
  induction tree generalizing s ν with
  | leaf b =>
    apply leafMass_le_potential f budget q s hν _ b
    simpa [DecisionTree.depth] using hs
  | node coordinate zero one ihz iho =>
    rcases coordinate with ⟨i, j⟩
    have hsz : (∑ k, spentUpdate s i k) + zero.depth ≤ q := by
      rw [sum_spentUpdate]
      simp only [DecisionTree.depth] at hs
      omega
    have hso : (∑ k, spentUpdate s i k) + one.depth ≤ q := by
      rw [sum_spentUpdate]
      simp only [DecisionTree.depth] at hs
      omega
    calc
      _ ≤ (2 : ℝ) ^ (q / (budget + 1)) *
          potential f budget (spentUpdate s i) (blockUpdate ν i j false) +
          (2 : ℝ) ^ (q / (budget + 1)) *
          potential f budget (spentUpdate s i) (blockUpdate ν i j true) :=
        add_le_add (ihz _ _ (blockUpdate_nonnegative hν i j false) hsz)
          (iho _ _ (blockUpdate_nonnegative hν i j true) hso)
      _ = (2 : ℝ) ^ (q / (budget + 1)) *
          (potential f budget (spentUpdate s i) (blockUpdate ν i j false) +
          potential f budget (spentUpdate s i) (blockUpdate ν i j true)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (potential_split f budget s hν i j)
        (pow_nonneg (by norm_num) _)

theorem finite_direct_product (f : BoolFn T) (budget q : ℕ) (β : ℝ)
    (tree : DecisionTree (I × T) (I → Bool)) (ν : I → Weight (Input T))
    (hν : ∀ i, Nonnegative (ν i)) (_hβ : 0 ≤ β)
    (hhard : ∀ i, opt f budget (ν i) ≤ β) (hdepth : tree.depth ≤ q) :
    productScore f tree ν ≤ (2 : ℝ) ^ (q / (budget + 1)) * β ^ Fintype.card I := by
  have h := productScore_le_potential f budget q tree (fun _ => 0) ν hν (by simpa using hdepth)
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
  change (∏ i, localPotential f budget 0 (ν i)) ≤ _
  simp only [localPotential, Nat.zero_le, if_true, Nat.sub_zero]
  calc
    (∏ i, opt f budget (ν i)) ≤ ∏ _i : I, β :=
      Finset.prod_le_prod (fun i _ => opt_nonnegative f budget (hν i)) (fun i _ => hhard i)
    _ = _ := by simp

def jointWeight (ν : I → Weight (Input T)) (x : I → Input T) : ℝ :=
  ∏ i, ν i (x i)

def jointScore (f : BoolFn T) (tree : DecisionTree (I × T) (I → Bool))
    (ν : I → Weight (Input T)) : ℝ :=
  ∑ x : I → Input T,
    if tree.eval (fun p => x p.1 p.2) = (fun i => f (x i)) then jointWeight ν x else 0

omit [Fintype T] [DecidableEq T] in
theorem jointWeight_blockUpdate (ν : I → Weight (Input T))
    (i : I) (j : T) (b : Bool) (x : I → Input T) :
    jointWeight (blockUpdate ν i j b) x =
      if x i j = b then jointWeight ν x else 0 := by
  by_cases hb : x i j = b
  · simp only [hb, if_true, jointWeight]
    apply Finset.prod_congr rfl
    intro k _
    by_cases hk : k = i
    · subst k
      simp [blockUpdate, queried, restrict, hb]
    · simp [blockUpdate, hk]
  · simp only [hb, if_false, jointWeight]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [blockUpdate, queried, restrict, hb]

theorem jointScore_leaf (f : BoolFn T) (b : I → Bool)
    (ν : I → Weight (Input T)) :
    jointScore f (.leaf b) ν = ∏ i, labelMass f (ν i) (b i) := by
  simp only [jointScore, DecisionTree.eval, labelMass, mass, restrict]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.prod_ite_zero]
  have he : b = (fun i => f (x i)) ↔ ∀ i, f (x i) = b i := by
    constructor
    · intro h i
      exact (congrFun h i).symm
    · intro h
      exact funext fun i => (h i).symm
  simp only [he, jointWeight]

theorem jointScore_node (f : BoolFn T) (i : I) (j : T)
    (zero one : DecisionTree (I × T) (I → Bool)) (ν : I → Weight (Input T)) :
    jointScore f (.node (i, j) zero one) ν =
      jointScore f zero (blockUpdate ν i j false) +
        jointScore f one (blockUpdate ν i j true) := by
  simp only [jointScore, DecisionTree.eval, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [jointWeight_blockUpdate, jointWeight_blockUpdate]
  by_cases h : x i j = true
  · simp [h]
  · have hfalse : x i j = false := Bool.eq_false_of_not_eq_true h
    simp [hfalse]

/-- The recursive quantity in the potential proof is exactly the finite weighted
probability of the actual query tree producing every block's correct answer. -/
theorem jointScore_eq_productScore (f : BoolFn T)
    (tree : DecisionTree (I × T) (I → Bool)) (ν : I → Weight (Input T)) :
    jointScore f tree ν = productScore f tree ν := by
  induction tree generalizing ν with
  | leaf b => exact jointScore_leaf f b ν
  | node coordinate zero one ihz iho =>
    rcases coordinate with ⟨i, j⟩
    rw [jointScore_node, ihz, iho]
    rfl

theorem jointScore_direct_product (f : BoolFn T) (budget q : ℕ) (β : ℝ)
    (tree : DecisionTree (I × T) (I → Bool)) (ν : I → Weight (Input T))
    (hν : ∀ i, Nonnegative (ν i)) (hβ : 0 ≤ β)
    (hhard : ∀ i, ∀ single : DecisionTree T Bool,
      single.depth ≤ budget → score f (ν i) single ≤ β)
    (hdepth : tree.depth ≤ q) :
    jointScore f tree ν ≤ (2 : ℝ) ^ (q / (budget + 1)) * β ^ Fintype.card I := by
  rw [jointScore_eq_productScore]
  exact finite_direct_product f budget q β tree ν hν hβ
    (fun i => opt_le_of_tree_bound f budget (ν i) β (hhard i)) hdepth

theorem randomized_direct_product (f : BoolFn T) (budget q : ℕ) (β : ℝ)
    {A : Type*} [Fintype A] (trees : A → DecisionTree (I × T) (I → Bool))
    (weight : A → ℝ) (ν : I → Weight (Input T))
    (hweight : ∀ a, 0 ≤ weight a) (hweight_sum : ∑ a, weight a = 1)
    (hν : ∀ i, Nonnegative (ν i)) (hβ : 0 ≤ β)
    (hhard : ∀ i, ∀ single : DecisionTree T Bool,
      single.depth ≤ budget → score f (ν i) single ≤ β)
    (hdepth : ∀ a, (trees a).depth ≤ q) :
    (∑ a, weight a * jointScore f (trees a) ν) ≤
      (2 : ℝ) ^ (q / (budget + 1)) * β ^ Fintype.card I := by
  calc
    _ ≤ ∑ a, weight a * ((2 : ℝ) ^ (q / (budget + 1)) * β ^ Fintype.card I) :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
        (jointScore_direct_product f budget q β (trees a) ν hν hβ hhard (hdepth a))
        (hweight a)
    _ = _ := by rw [← Finset.sum_mul, hweight_sum, one_mul]

omit [Fintype T] [DecidableEq T] [DecidableEq I] in
theorem jointWeight_nonnegative {ν : I → Weight (Input T)}
    (hν : ∀ i, Nonnegative (ν i)) (x : I → Input T) : 0 ≤ jointWeight ν x :=
  Finset.prod_nonneg fun i _ => hν i (x i)

theorem jointWeight_mass (ν : I → Weight (Input T)) :
    mass (jointWeight ν) = ∏ i, mass (ν i) := by
  exact (Fintype.prod_sum ν).symm

section ListOutput

variable {K : Type*} [Fintype K]

noncomputable def listScore (f : BoolFn T)
    (tree : DecisionTree (I × T) (K → I → Bool)) (ν : I → Weight (Input T)) : ℝ := by
  classical
  exact ∑ x : I → Input T,
    if ∃ k, tree.eval (fun p => x p.1 p.2) k = (fun i => f (x i))
      then jointWeight ν x else 0

theorem listScore_le_sum (f : BoolFn T)
    (tree : DecisionTree (I × T) (K → I → Bool)) (ν : I → Weight (Input T))
    (hν : ∀ i, Nonnegative (ν i)) :
    listScore f tree ν ≤ ∑ k, jointScore f (tree.mapOutput (fun output => output k)) ν := by
  classical
  simp only [listScore, jointScore, DecisionTree.eval_mapOutput]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : ∃ k, tree.eval (fun p => x p.1 p.2) k = (fun i => f (x i))
  · simp only [hx, if_true]
    obtain ⟨k, hk⟩ := hx
    calc
      jointWeight ν x =
          (if tree.eval (fun p => x p.1 p.2) k = (fun i => f (x i))
            then jointWeight ν x else 0) := by simp [hk]
      _ ≤ _ := by
        apply Finset.single_le_sum (s := (Finset.univ : Finset K))
          (f := fun a => if tree.eval (fun p => x p.1 p.2) a = (fun i => f (x i))
            then jointWeight ν x else 0)
        · intro a _
          split_ifs
          · exact jointWeight_nonnegative hν x
          · exact le_refl 0
        · exact Finset.mem_univ k
  · simp only [hx, if_false]
    exact Finset.sum_nonneg fun a _ => by
      split_ifs <;> first | exact jointWeight_nonnegative hν x | exact le_refl 0

/-- A depth-`q` tree returning at most `card K` candidates can contain the correct
answer vector with probability at most `card K` times the direct-product bound. -/
theorem list_direct_product (f : BoolFn T) (budget q : ℕ) (β : ℝ)
    (tree : DecisionTree (I × T) (K → I → Bool)) (ν : I → Weight (Input T))
    (hν : ∀ i, Nonnegative (ν i)) (hβ : 0 ≤ β)
    (hhard : ∀ i, ∀ single : DecisionTree T Bool,
      single.depth ≤ budget → score f (ν i) single ≤ β)
    (hdepth : tree.depth ≤ q) :
    listScore f tree ν ≤ (Fintype.card K : ℝ) *
      ((2 : ℝ) ^ (q / (budget + 1)) * β ^ Fintype.card I) := by
  calc
    _ ≤ ∑ k, jointScore f (tree.mapOutput (fun output => output k)) ν :=
      listScore_le_sum f tree ν hν
    _ ≤ ∑ _k : K, ((2 : ℝ) ^ (q / (budget + 1)) * β ^ Fintype.card I) :=
      Finset.sum_le_sum fun k _ =>
        jointScore_direct_product f budget q β _ ν hν hβ hhard (by simpa using hdepth)
    _ = _ := by simp

theorem randomized_list_direct_product (f : BoolFn T) (budget q : ℕ) (β : ℝ)
    {A : Type*} [Fintype A] (trees : A → DecisionTree (I × T) (K → I → Bool))
    (weight : A → ℝ) (ν : I → Weight (Input T))
    (hweight : ∀ a, 0 ≤ weight a) (hweight_sum : ∑ a, weight a = 1)
    (hν : ∀ i, Nonnegative (ν i)) (hβ : 0 ≤ β)
    (hhard : ∀ i, ∀ single : DecisionTree T Bool,
      single.depth ≤ budget → score f (ν i) single ≤ β)
    (hdepth : ∀ a, (trees a).depth ≤ q) :
    (∑ a, weight a * listScore f (trees a) ν) ≤ (Fintype.card K : ℝ) *
      ((2 : ℝ) ^ (q / (budget + 1)) * β ^ Fintype.card I) := by
  calc
    _ ≤ ∑ a, weight a * ((Fintype.card K : ℝ) *
        ((2 : ℝ) ^ (q / (budget + 1)) * β ^ Fintype.card I)) :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
        (list_direct_product f budget q β (trees a) ν hν hβ hhard (hdepth a)) (hweight a)
    _ = _ := by rw [← Finset.sum_mul, hweight_sum, one_mul]

end ListOutput

end Product

/-- Finite averaging swaps the input distribution and the randomized tree. -/
theorem expected_score_comm (f : BoolFn T) (ν : Weight (Input T))
    {A : Type*} [Fintype A] (trees : A → DecisionTree T Bool) (weight : A → ℝ) :
    (∑ a, weight a * score f ν (trees a)) =
      ∑ x, ν x * ∑ a, if (trees a).eval x = f x then weight a else 0 := by
  simp only [score, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

theorem expected_score_lower (f : BoolFn T) {ν : Weight (Input T)}
    (hν : Nonnegative ν) {A : Type*} [Fintype A]
    (trees : A → DecisionTree T Bool) (weight : A → ℝ) (δ : ℝ)
    (hcorrect : ∀ x, δ ≤ ∑ a, if (trees a).eval x = f x then weight a else 0) :
    δ * mass ν ≤ ∑ a, weight a * score f ν (trees a) := by
  rw [expected_score_comm, mass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hcorrect x) (hν x)

/-- A hard finite input distribution rules out a worst-input bounded-error
algorithm. This is the elementary (averaging) direction of Yao's principle. -/
theorem not_hasRandomizedBound_of_hard_distribution (f : BoolFn T) (q : ℕ)
    (ν : Weight (Input T)) (hν : Nonnegative ν) (hmass : mass ν = 1) (β : ℝ)
    (hβ : β < (2 : ℝ) / 3)
    (hhard : ∀ tree : DecisionTree T Bool, tree.depth ≤ q → score f ν tree ≤ β) :
    ¬ HasRandomizedBound f q := by
  rintro ⟨m, trees, weight, hdepth, hweight, hweight_sum, hcorrect⟩
  have hlo := expected_score_lower f hν trees weight ((2 : ℝ) / 3) hcorrect
  rw [hmass, mul_one] at hlo
  have hhi : (∑ a, weight a * score f ν (trees a)) ≤ β := by
    calc
      _ ≤ ∑ a, weight a * β := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (hhard (trees a) (hdepth a)) (hweight a)
      _ = β := by rw [← Finset.sum_mul, hweight_sum, one_mul]
  linarith

theorem R_gt_of_hard_distribution (f : BoolFn T) (q : ℕ)
    (ν : Weight (Input T)) (hν : Nonnegative ν) (hmass : mass ν = 1) (β : ℝ)
    (hβ : β < (2 : ℝ) / 3)
    (hhard : ∀ tree : DecisionTree T Bool, tree.depth ≤ q → score f ν tree ≤ β) :
    q < R f := by
  apply Nat.lt_of_not_ge
  intro h
  exact not_hasRandomizedBound_of_hard_distribution f q ν hν hmass β hβ hhard
    ((hasRandomizedBound_iff_R_le).2 h)

end DirectProduct
end QueryComplexity
