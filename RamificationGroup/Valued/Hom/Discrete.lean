import RamificationGroup.Valued.Hom.Basic
import Mathlib.FieldTheory.Galois

section

-- `key def : If L/K  a finite field extension of local field, then there exist a extension of valuation`, see Maria and Phillip, `discrete_valuation_ring.extensions`

def DiscretelyValued.extensionFiniteDimension {K} (L) [Field K] [Field L] [DiscretelyValued K] [Algebra K L] [FiniteDimensional K L] : DiscretelyValued L  := sorry

-- instance : Valued L

-- `key theorem: If L/K is a finite field extension + more conditions, then any 2 extension of valuations from K on L are equivalent`; Discrete Valuations are equal
theorem Valuation.isEquiv_of_finiteDimensional {K L : Type*} [Field K] [Field L] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] [vK : DiscretelyValued K] [vL : Valued L Γ] [ValAlgebra K L] [FiniteDimensional K L]
 : vL.v.IsEquiv (vK.extensionFiniteDimension L).v := sorry
-- DiscreteValuation.Extension.integralClosure_eq_integer see Maria

variable {K L : Type*} [Field K] [Field L] [DiscretelyValued K] [a : Algebra K L] [FiniteDimensional K L]


instance : DiscretelyValued L := sorry -- see Maria and Phillip

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

-- should instances of Discretely Valued L, K' auto generated from K? also [ValAlgebra K L]
instance : ValAlgebra K K' := sorry
instance : ValAlgebra K' L := sorry
-- `instance IsValScalarTower K K' L`






-- any alg map preserves valuation, thus we can define a function input alg map output val alg map


-- some Unique instance?


-- Unique instance in the case of Local Fields, which comes from uniqueness of extension of valuation.


-- `Canonical Isom between AlgEquiv and ValAlgEquiv!`
variable {K L : Type*} [Field K] [Field L] {Γ : Type*} [vK : DiscretelyValued K] [vL : DiscretelyValued L] [ValAlgebra K L] [FiniteDimensional K L]

def AlgEquiv.toValAlgEquiv : (L ≃ₐ[K] L) ≃* (L ≃ₐv[K] L) := sorry

end
