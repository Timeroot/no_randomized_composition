import QueryComplexity.ProductPosteriors
import QueryComplexity.FiniteAveraging

open scoped BigOperators

namespace QueryComplexity.ProductPosteriors

open FiniteProbability

variable {I X Y P H : Type*} [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y]
  [Fintype P] [Fintype H]

theorem joint_pushforward (ν : I → X → ℝ) (g : I → X → Y) (y : I → Y) :
    pushforward (jointWeight ν) (fun x i => g i (x i)) y =
      jointWeight (fun i => pushforward (ν i) (g i)) y := by
  classical
  simp only [pushforward, jointWeight]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.prod_ite_zero]
  simp only [funext_iff]

theorem joint_pushforward_expectation (ν : I → X → ℝ) (g : I → X → Y)
    (φ : (I → Y) → ℝ) :
    (∑ y, jointWeight (fun i => pushforward (ν i) (g i)) y * φ y) =
      ∑ x, jointWeight ν x * φ (fun i => g i (x i)) := by
  simp_rw [← joint_pushforward]
  exact sum_pushforward_mul _ _ _

def sourceSplit : (I → P × H) ≃ (I → P) × (I → H) where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun x := fun i => (x.1 i, x.2 i)
  left_inv x := by funext i; rfl
  right_inv x := by cases x; rfl

theorem uniform_joint (h : I → H) :
    jointWeight (fun _ => uniformWeight H) h = uniformWeight (I → H) h := by
  simp [jointWeight, uniformWeight, Fintype.card_fun, Nat.cast_pow]

theorem product_source_expectation (ν : P → ℝ) (φ : (I → P) → (I → H) → ℝ) :
    (∑ x : I → P × H, jointWeight (fun _ pair => ν pair.1 * uniformWeight H pair.2) x *
      φ (fun i => (x i).1) (fun i => (x i).2)) =
      ∑ p : I → P, jointWeight (fun _ => ν) p * average (fun h : I → H => φ p h) := by
  have he := (sourceSplit (I := I) (P := P) (H := H)).sum_comp
    (fun x : (I → P) × (I → H) => jointWeight (fun _ => ν) x.1 *
      uniformWeight (I → H) x.2 * φ x.1 x.2)
  simp only [sourceSplit, Equiv.coe_fn_mk] at he
  calc
    _ = ∑ x : I → P × H, jointWeight (fun _ => ν) (fun i => (x i).1) *
        uniformWeight (I → H) (fun i => (x i).2) * φ (fun i => (x i).1) (fun i => (x i).2) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← uniform_joint]
      simp only [jointWeight, Finset.prod_mul_distrib]
    _ = _ := by
      rw [he, Fintype.sum_prod_type]
      simp only [average, Finset.mul_sum, mul_assoc]

end QueryComplexity.ProductPosteriors
