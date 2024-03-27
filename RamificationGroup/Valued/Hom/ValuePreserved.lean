import RamificationGroup.Valued.Hom.Defs

variable {R S : Type*} {ΓR ΓS : outParam Type*} [Ring R] [Ring S]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS]
  [vR : Valued R ΓR] [vS : Valued S ΓS]
variable {F : Type*} [FunLike F R S] [ValRingHomClass F R S]

/-
1. how to add completeness
2. should parametrized over `ValRingHomClass`, right?
-/

theorem ringhom_preserve_valuation (f : F) : vR.v.IsEquiv (vS.v.comap f) := by
  sorry
