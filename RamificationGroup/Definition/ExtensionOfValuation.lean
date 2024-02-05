import RamificationGroup.Definition.CompleteValuationRing

class ValuationExtension {R₁ R₂} [CommRing R₁] [CommRing R₂] {Γ₁ Γ₂} [LinearOrderedCommMonoidWithZero Γ₁] [LinearOrderedCommMonoidWithZero Γ₂] [Algebra R₁ R₂] (v₁ : Valuation R₁ Γ₁) (v₂ : Valuation R₂ Γ₂) where
  val_map : Γ₁ →*₀o Γ₂
  val_extn : ∀ x : R₁, v₂ ((algebraMap R₁ R₂) x) = val_map (v₁ x)

-- `def of EquivToDiscrete`

-- `finite extension of (equiv to) discerete valuation is still (equiv to) discrete`


-- def of EquivToTrivial

-- finite ext of trivial val is still trivial?


-- `Valuation on any field is either trivial or supp = 0`
