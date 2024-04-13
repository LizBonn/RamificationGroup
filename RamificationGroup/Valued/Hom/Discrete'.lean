import RamificationGroup.Valued.Hom.ValExtension
import Mathlib.FieldTheory.IntermediateField
import LocalClassFieldTheory.DiscreteValuationRing.Extensions

open Valuation Valued DiscreteValuation

-- an instance of Valued for intermediate field (??)
-- two instance of IsValExtension for maria's valued, K to K' and K' to K''

namespace DiscreteValuation

variable {K K' L : Type*} {ΓK ΓK' : outParam Type*} [Field K] [Field L]
[vK : Valued K ℤₘ₀] [CompleteSpace K]
[IsDiscrete vK.v] [Algebra K L] {K' K'' : IntermediateField K L} [FiniteDimensional K K'] [FiniteDimensional K K'']

-- `Maybe this is bad`
noncomputable scoped instance intermidateFieldValued : Valued K' ℤₘ₀ := DiscreteValuation.Extension.valued K K'

scoped instance intermidateFieldIsValExtension : IsValExtension K K' where
  val_isEquiv_comap := sorry

scoped instance intermidateFieldIsDiscrete: IsDiscrete (DiscreteValuation.Extension.valued K K').v := DiscreteValuation.Extension.isDiscrete_of_finite K K'

end DiscreteValuation

/-
variable {K K' L : Type*} {ΓK ΓK' : outParam Type*} [Field K] [Field K'] [Field L]
[vK : Valued K ℤₘ₀] [vL : Valued L ℤₘ₀]
[IsDiscrete vK.v] [IsDiscrete vL.v] [Algebra K L] [IsValExtension K L] [FiniteDimensional K L] {K' : IntermediateField K L}

--{H : Subgroup (L ≃ₐ[K] L)} [H.Normal]

namespace DiscreteValuation
-- should be in file talking about both Discrete and ValAlgHom, probably Hom.Discrete
scoped instance valuedIntermediateField : Valued K' ℤₘ₀ := sorry

scoped instance : IsDiscrete ((valuedIntermediateField (K':= K')).v) := sorry

#synth IsScalarTower K K' L

#synth Algebra K' L


scoped instance : IsValExtension K' L := sorry
#synth Algebra K K'
scoped instance : IsValExtension K K' := sorry

end DiscreteValuation
-/
