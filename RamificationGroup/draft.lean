import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.FieldTheory.MinPoly.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

section

variable {A : Type*} [CommRing A] [IsDomain A] [DiscreteValuationRing A]
variable {p : Ideal A}
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type*} [Field L] [Algebra K L] [Algebra A L]
variable {B : Type*} [CommRing B] [Algebra B L] [IsIntegralClosure B A L]
                     [IsDomain B] [DiscreteValuationRing B]

theorem PROP18 (h1 : FiniteDimensional.finrank K L = (n : ℕ)) {x : B} [Irreducible x] :
IsEisensteinAt (minpoly x K) p := by sorry
end
