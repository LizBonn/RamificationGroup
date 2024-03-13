import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

variable (A : Type _) (B : Type _) [CommSemiring A] [Semiring B] [Algebra A B]

variable {x : B} (h : Algebra.adjoin A {x} = ⊤)

#synth Module A B

#check LinearEquiv.ofTop
#check LinearEquiv.ofTop (Algebra.adjoin A {x}) h
def AlgEquiv.ofAdjoinSingleton : Algebra.adjoin A {x} ≃ₐ[A] B := sorry
