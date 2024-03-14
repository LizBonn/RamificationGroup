/-
GOAL : construct `S ≃ₐ B` for `S = ⊤ : Subalgebra A B`

might not be good to use `LinearEquiv.ofTop`

-/

import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

variable {A : Type _} {B : Type _} [CommSemiring A] [Semiring B] [Algebra A B]
variable {S : Subalgebra A B} (hS : S = ⊤)
variable {x : B} (hx : Algebra.adjoin A {x} = ⊤)

def LinearEquiv.ofSubalgebraEqTop : S ≃ₗ[A] B :=
  LinearEquiv.ofTop (Subalgebra.toSubmodule S) (Algebra.toSubmodule_eq_top.mpr hS)

def AlgEquiv.ofTop : S ≃ₐ[A] B := by
  apply AlgEquiv.ofLinearEquiv (LinearEquiv.ofSubalgebraEqTop hS)
  · unfold LinearEquiv.ofSubalgebraEqTop
    sorry
  · sorry
