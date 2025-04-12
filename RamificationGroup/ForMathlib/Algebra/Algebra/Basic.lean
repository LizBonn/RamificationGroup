import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.FiniteType

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

theorem Algebra.isIntegral_iff_isIntegral :
  Algebra.IsIntegral R A ↔ (algebraMap R A).IsIntegral := by
  rw [Algebra.isIntegral_def]; rfl

instance instAlgebraFiniteTypeToIsNoetherian (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [IsNoetherian R A] :
  Algebra.FiniteType R A where
    out := by
      apply Subalgebra.fg_of_fg_toSubmodule
      rw [Algebra.top_toSubmodule]
      apply isNoetherian_def.mp
      assumption
