import Mathlib.RingTheory.PowerBasis

namespace PowerBasis

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
{S' : Type*} [Semiring S'] [Algebra R S']

theorem algEquiv_ext (pb : PowerBasis R S) {f g : S ≃ₐ[R] S'} (h : f pb.gen = g pb.gen) :
  f = g := by
  ext x
  rw [show f x = g x ↔ f.toAlgHom x = g.toAlgHom x by rfl]
  revert x
  rw [← AlgHom.ext_iff]
  apply algHom_ext _ h
