import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

variable (A : Type _) (B : Type _) [CommSemiring A] [Semiring B] [Algebra A B]

variable {x : B} (h : Algebra.adjoin A {x} = ⊤)

def AlgEquiv.ofAdjoinSingleton : Algebra.adjoin A {x} ≃ₐ[A] B := sorry
