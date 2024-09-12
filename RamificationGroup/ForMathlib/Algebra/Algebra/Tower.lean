import Mathlib.Algebra.Algebra.Tower

namespace AlgEquiv

def restrictScalarsHom (R : Type*) {S A: Type*} [CommSemiring R] [CommSemiring S] [Semiring A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A] :
  (A ≃ₐ[S] A) →* (A ≃ₐ[R] A) where
    toFun := restrictScalars R
    map_one' := rfl
    map_mul' _ _ := by
      ext
      rfl

theorem restrictScalarsHom_injective (R : Type*) {S A: Type*} [CommSemiring R] [CommSemiring S] [Semiring A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A] : Function.Injective (restrictScalarsHom R (S := S) (A := A)):= by sorry

end AlgEquiv
