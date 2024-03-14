import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Topology.Algebra.Valuation
import Mathlib.Algebra.Order.WithZero
import Mathlib.Algebra.Order.Group.TypeTags
import Mathlib.FieldTheory.Galois
import LocalClassFieldTheory.LocalField

open DiscreteValuation

variable {K L} [Field K] [Field L] [Algebra K L] [vK : Valued K ℤₘ₀] [vL : Valued L ℤₘ₀]
-- and some more instances



variable (h : vK.v.IsEquiv (vL.v.comap (algebraMap K L)))


structure ValRingHom (R S : Type*) {ΓR ΓS : outParam Type*} [Ring R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS]
  [vR : Valued R ΓR] [vS : Valued S ΓS] extends RingHom R S where
  val_isEquiv : vR.v.IsEquiv (vS.v.comap toRingHom)

infixr:25 " →+*v " => ValRingHom
