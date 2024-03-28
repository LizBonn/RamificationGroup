import RamificationGroup.Valued.Hom.Defs
import Mathlib.FieldTheory.Galois

open DiscreteValuation

-- variable (K L ΓK ΓL) [Field K] [Field L] [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL] [Valued K ΓK] [vL : Valued L ΓL] [ValAlgebra K L]
-- variable (K' : IntermediateField K L)

-- instance : Valued K' ΓL := Valued.mk' (vL.v.comap (algebraMap K' L))

-- instance : ValAlgebra K' L where
--   toFun := _
--   map_one' := _
--   map_mul' := _
--   map_zero' := _
--   map_add' := _
--   monotone' := _
--   continuous_toFun := _
--   val_isEquiv_comap' := _
--   smul := _
--   commutes' := _
--   smul_def' := _

-- instance : ValAlgebra K K' where
--   toFun := sorry
--   map_one' := sorry
--   map_mul' := sorry
--   map_zero' := sorry
--   map_add' := sorry
--   monotone' := sorry
--   continuous_toFun := sorry
--   val_isEquiv_comap' := sorry
--   smul := sorry
--   commutes' := sorry
--   smul_def' := sorry

namespace HerbrandFunction

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [ValAlgebra R S]

def phi (K L : Type*) [CommRing K] [Ring L] [Algebra K L] : ℚ → ℚ := sorry

scoped notation:max  " φ_[" L:max "/" K:max "](" x:max ") " => phi K L x

def psi (K L : Type*) [CommRing K] [Ring L] [Algebra K L] : ℚ → ℚ := sorry

scoped notation:max  " ψ_[" L:max "/" K:max "](" x:max ") " => psi K L x

variable (K L : Type*) [CommRing K] [Ring L] [Algebra K L] (x : ℕ)
#check φ_[L/K](x)
#check ψ_[L/K](x)
end HerbrandFunction
