import RamificationGroup.Valued.Hom.Defs
import Mathlib.FieldTheory.IntermediateField

open Valuation Valued DiscreteValuation

variable {K K' L : Type*} {ΓK ΓK' : outParam Type*} [Field K] [Field K'] [Field L]
[vK : Valued K ℤₘ₀] [vL : Valued L ℤₘ₀]
[IsDiscrete vK.v] [IsDiscrete vL.v] [ValAlgebra K L] [FiniteDimensional K L] {K' : IntermediateField K L}

--{H : Subgroup (L ≃ₐ[K] L)} [H.Normal]

namespace DiscreteValuation
-- should be in file talking about both Discrete and ValAlgHom, probably Hom.Discrete
scoped instance valuedIntermediateField : Valued K' ℤₘ₀ := sorry

scoped instance : IsDiscrete ((valuedIntermediateField (K':= K')).v) := sorry

#synth IsScalarTower K K' L

#synth Algebra K' L

attribute [-instance] Subtype.preorder

scoped instance : ValAlgebra K' L :=
  {
    Subalgebra.toAlgebra K'.toSubalgebra with
    monotone' := sorry
    val_isEquiv_comap' := sorry
    continuous_toFun := sorry
  }
#synth Algebra K K'
scoped instance : ValAlgebra K K' :=
  {
    IntermediateField.algebra K' with
    monotone' := sorry
    val_isEquiv_comap' := sorry
    continuous_toFun := sorry
  }

end DiscreteValuation
