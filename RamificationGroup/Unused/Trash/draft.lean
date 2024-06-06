import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Algebra.Basic
import Mathlib.FieldTheory.Galois
import RamificationGroup.Unused.Definition.LowerNumbering

section

open Polynomial RingHom IsDedekindDomain FiniteDimensional DiscreteValuationRing Ideal Algebra

variable {A : Type*} [CommRing A] [IsDomain A] [DiscreteValuationRing A]
variable {p : Ideal A}
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type*} [Field L] [Algebra K L] [Module.Finite K L] [Algebra A L] [IsScalarTower A K L]
variable {B : Type*} [CommRing B] [Algebra B L] [Algebra A B] [Algebra K B] [IsIntegralClosure B A L]
                     [IsDomain B] [DiscreteValuationRing B] [SMulCommClass B K L] [IsScalarTower A B L]
(va : HeightOneSpectrum A) (vb : HeightOneSpectrum B)
[HMul PartENat ℕ PartENat]

variable {a : A}

theorem Prop18 {x : B} (h0 : Irreducible x) (h1 : ∀ a : A, (addVal A a) * (finrank K L) = addVal B (algebraMap A B a)) :
(ker (aeval x)) = (Ideal.span {LinearMap.charpoly (lsmul A K L x)}) := by sorry


def aaa (f : ℕ → ℕ) := ∀ x y, f (x + y) = f x + f y ∧ ∀ x c, f (c * x) = c * f x
