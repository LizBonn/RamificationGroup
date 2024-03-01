import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.FieldTheory.MinPoly.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

section

open Polynomial RingHom IsDedekindDomain FiniteDimensional Ideal

variable {A : Type*} [CommRing A] [IsDomain A] [DiscreteValuationRing A]
variable {p : Ideal A}
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type*} [Field L] [Algebra K L] [Algebra A L]
variable {B : Type*} [CommRing B] [Algebra B L] [Algebra A B] [Algebra K B] [IsIntegralClosure B A L]
                     [IsDomain B] [DiscreteValuationRing B]
(va : HeightOneSpectrum A) {vb : HeightOneSpectrum B}
{f : A →+* B}

theorem Prop18 {x : B} (h0 : Irreducible x) (h2 : (∀ x ∈ A, va.intValuation (x : A) = vb.intValuation (x : B) * (e ^ (finrank K L)))) :
(ker (aeval x)) = (map C p : Ideal A[X]) := by sorry
end
