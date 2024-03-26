import RamificationGroup.Valued.Hom.Defs
import Mathlib.FieldTheory.Galois

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

def HerbrandPhi : ℚ → ℚ := sorry

def HerbrandPsi : ℚ → ℚ := sorry
