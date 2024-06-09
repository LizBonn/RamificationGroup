import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Data.Polynomial.Induction

section semiring
variable {A : Type _} {B : Type _} [CommSemiring A] [Semiring B] [Algebra A B]

def AlgEquiv.ofTop {S : Subalgebra A B} (hS : S = ⊤) : S ≃ₐ[A] B := { S.val with
    invFun := fun x ↦ ⟨x, hS.symm ▸ trivial⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
  }

section adjoin
namespace Algebra
open Polynomial
variable {x : B}

theorem pow_mem_adjoin_singleton (n : ℕ) : x ^ n ∈ adjoin A {x} := by
  induction' n with n ih
  · simp only [Nat.zero_eq, pow_zero]
    apply one_mem
  · rw [pow_succ]
    apply mul_mem (self_mem_adjoin_singleton _ x) ih


end Algebra
end adjoin

end semiring
