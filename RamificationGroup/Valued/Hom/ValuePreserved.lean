import RamificationGroup.Valued.Hom.Defs

variable {K L : Type*} {ΓK: outParam Type*} [Ring K] [Ring L]
  [LinearOrderedCommGroupWithZero ΓK] [vK : Valued K ΓK]
variable {f : K →+* L}

/-
1. how to add completeness
2. should be parametrized over `ValRingHomClass`, right?
-/
