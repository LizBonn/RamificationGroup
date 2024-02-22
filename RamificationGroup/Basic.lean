import Mathlib.Topology.Algebra.Valuation
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.FieldTheory.Galois
import Mathlib.Algebra.Order.Group.TypeTags
import Mathlib.Algebra.Order.Hom.Ring

open DiscreteValuation

class DiscretelyValued (R : Type*) [Ring R] extends Valued R ℤₘ₀ where
  v_is_surj : (v.toFun).Surjective

instance {R : Type*} {Γ : outParam Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ] [Valued R Γ]: Preorder R := sorry

structure ValRingHom (R S : Type*) {ΓR ΓS : outParam Type*} [Ring R] [Ring S]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS]
  [vR : Valued R ΓR] [vS : Valued S ΓS] extends OrderRingHom R S, ContinuousMap R S where
  val_isEquiv_comap : vR.v.IsEquiv (vS.v.comap toOrderRingHom.toRingHom)

class ValAlgebra (R A : Type*) {ΓR ΓA : outParam Type*} [CommRing R] [Ring A] [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [vR : Valued R ΓR] [vA : Valued A ΓA] extends ValRingHom R A, Algebra R A

variable {K L : Type*} [Field K] [Field L] [DiscretelyValued K] [a : Algebra K L] [FiniteDimensional K L]


instance : DiscretelyValued L := sorry 

instance : ValAlgebra K L where
  toFun := _
  map_one' := _
  map_mul' := _
  map_zero' := _
  map_add' := _
  monotone' := sorry
  continuous_toFun := sorry
  val_isEquiv_comap := sorry
  smul := a.smul
  commutes' := a.commutes'
  smul_def' := a.smul_def'


variable (K' : IntermediateField K L) [IsGalois K L]

#synth IsScalarTower K K' L
#synth ValAlgebra K K'
#synth ValAlgebra K' L

instance : ValAlgebra K K' := sorry
instance : ValAlgebra K' L := sorry
-- `instance IsValScalarTower K K' L`




open DiscreteValuation

#synth LinearOrderedCommGroupWithZero ℤₘ₀
