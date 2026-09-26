import Mathlib.Logic.Function.Basic

/-!
# Block composition

An outer function reads one output of the inner function for each outer
coordinate. The combined input coordinates form a Cartesian product.
-/

namespace Function

universe u v w x y

/-- Apply `g` to each input block, then apply `f` to the resulting outputs. -/
def blockComp {I : Type u} {J : Type v} {A : Type w} {B : Type x} {C : Type y}
    (f : (I → B) → C) (g : (J → A) → B) : (I × J → A) → C :=
  fun input => f (fun i => g (fun j => input (i, j)))

@[simp] theorem blockComp_apply
    {I : Type u} {J : Type v} {A : Type w} {B : Type x} {C : Type y}
    (f : (I → B) → C) (g : (J → A) → B) (input : I × J → A) :
    blockComp f g input = f (fun i => g (fun j => input (i, j))) := rfl

end Function
