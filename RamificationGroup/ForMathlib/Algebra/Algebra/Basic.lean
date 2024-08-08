import Mathlib.RingTheory.IntegralClosure.Algebra.Defs

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

theorem Algebra.isIntegral_iff_isIntegral :
  Algebra.IsIntegral R A ↔ (algebraMap R A).IsIntegral := by
  rw [Algebra.isIntegral_def]; rfl
