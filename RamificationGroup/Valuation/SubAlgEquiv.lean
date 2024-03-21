import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Data.Polynomial.Induction

variable {A : Type _} {B : Type _} [CommSemiring A] [Semiring B] [Algebra A B]

def AlgEquiv.ofTop {S : Subalgebra A B} (hS : S = ⊤) : S ≃ₐ[A] B := { S.val with
    invFun := fun x ↦ ⟨x, hS.symm ▸ trivial⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
  }

namespace Algebra

section adjoin
open Polynomial
variable {x : B}

theorem pow_mem_adjoin_singleton (n : ℕ) : x ^ n ∈ adjoin A {x} := by
  induction' n with n ih
  · simp only [Nat.zero_eq, pow_zero]
    apply one_mem
  · rw [pow_succ]
    apply mul_mem (self_mem_adjoin_singleton _ x) ih

theorem aeval_C_mem_adjoin {a : A} {s : Set B}: aeval x (C a) ∈ adjoin A s := by
  rw [aeval_def, eval₂_C]
  exact Subalgebra.algebra'.proof_1 (adjoin A s) a

theorem aeval_mem_adjoin_singleton (f : A[X]) : aeval x f ∈ adjoin A {x} := by
  induction f using Polynomial.induction_on with
  | h_C a => apply aeval_C_mem_adjoin
  | h_add p q a b =>
    rw [aeval_add]
    apply add_mem a b
  | h_monomial n a h =>
    rw [pow_succ, mul_comm X, ← mul_assoc, aeval_mul, aeval_X]
    apply mul_mem h (self_mem_adjoin_singleton _ x)



end adjoin

end Algebra
