import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

variable {A : Type _} {B : Type _} [CommSemiring A] [Semiring B] [Algebra A B]
variable {S : Subalgebra A B} (hS : S = ⊤)
variable {x : B} (hx : Algebra.adjoin A {x} = ⊤)

def AlgEquiv.ofTop : S ≃ₐ[A] B := { S.val with
    invFun := fun x ↦ ⟨x, hS.symm ▸ trivial⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
  }
