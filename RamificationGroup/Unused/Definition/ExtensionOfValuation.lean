import RamificationGroup.Unused.Definition.CompleteValuationRing
import Mathlib.RingTheory.Valuation.Basic

section

variable {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂] {Γ₁ Γ₂ : Type*} [LinearOrderedCommGroupWithZero Γ₁] [LinearOrderedCommGroupWithZero Γ₂] [Algebra R₁ R₂] (v₁ : Valuation R₁ Γ₁) (v₂ : Valuation R₂ Γ₂)

def RingHom.liftValuationInteger (s : R₁ →+* R₂) (h : v₁.IsEquiv (v₂.comap s)) : 𝒪[v₁] →+* 𝒪[v₂] := sorry

def PreserveValuation {R₁ R₂} [CommRing R₁] [CommRing R₂] {Γ₁ Γ₂} [LinearOrderedCommMonoidWithZero Γ₁] [LinearOrderedCommMonoidWithZero Γ₂] (v₁ : Valuation R₁ Γ₁) (v₂ : Valuation R₂ Γ₂) (s : R₁ →+* R₂) : Prop := v₁.IsEquiv (v₂.comap s)

end

-- there are many many usage of Group should be Monoid in mathlib
class ValuationExtension {R₁ R₂} [CommRing R₁] [CommRing R₂] {Γ₁ Γ₂} [LinearOrderedCommMonoidWithZero Γ₁] [LinearOrderedCommMonoidWithZero Γ₂] [Algebra R₁ R₂] (v₁ : Valuation R₁ Γ₁) (v₂ : Valuation R₂ Γ₂) where
  val_map : Γ₁ →*₀o Γ₂
  val_extn : ∀ x : R₁, v₂ ((algebraMap R₁ R₂) x) = val_map (v₁ x)

-- I prefer this later definition
class ValuationExtension' {R₁ R₂} [CommRing R₁] [CommRing R₂] {Γ₁ Γ₂} [LinearOrderedCommMonoidWithZero Γ₁] [LinearOrderedCommMonoidWithZero Γ₂] [Algebra R₁ R₂] (v₁ : Valuation R₁ Γ₁) (v₂ : Valuation R₂ Γ₂) where
  val_extn : PreserveValuation v₁ v₂ (algebraMap _ _)


instance Algebra.liftValuationInteger {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂] {Γ₁ Γ₂ : Type*} [LinearOrderedCommGroupWithZero Γ₁] [LinearOrderedCommGroupWithZero Γ₂] [Algebra R₁ R₂] (v₁ : Valuation R₁ Γ₁) (v₂ : Valuation R₂ Γ₂) [ValuationExtension v₁ v₂] : Algebra 𝒪[v₁] 𝒪[v₂] := sorry

-- variable {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂] {Γ₁ Γ₂ : Type*} [LinearOrderedCommGroupWithZero Γ₁] [LinearOrderedCommGroupWithZero Γ₂] [Algebra R₁ R₂] (v₁ : Valuation R₁ Γ₁) (v₂ : Valuation R₂ Γ₂) [ValuationExtension v₁ v₂]
-- #synth Algebra 𝒪[v₁] (𝒪[v₂]⧸(𝓂[v₂]^2))


-- when R₁ R₂ are field
instance {R₁ R₂ : Type*} [Field R₁] [Field R₂] {Γ₁ Γ₂ : Type*} [LinearOrderedCommGroupWithZero Γ₁] [LinearOrderedCommGroupWithZero Γ₂] [Algebra R₁ R₂] (v₁ : Valuation R₁ Γ₁) (v₂ : Valuation R₂ Γ₂) [ValuationExtension v₁ v₂]: Algebra 𝓀[v₁] 𝓀[v₂] := sorry







-- `def of EquivToDiscrete`

-- `finite extension of (equiv to) discerete valuation is still (equiv to) discrete`


-- def of EquivToTrivial

-- finite ext of trivial val is still trivial?


-- `Valuation on any field is either trivial or supp = 0`


-- `key theorem: If L/K is a finite field extension + more conditions, then any 2 extension of valuations from K on L are equivalent`
theorem Valuation.isEquiv_of_finiteDimensional_of_valuationExtension {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {Γ Γ₁ Γ₂ : Type*} [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Γ₁]
[LinearOrderedCommGroupWithZero Γ₂]
(v : Valuation K Γ) (v₁ : Valuation L Γ₁) (v₂ : Valuation L Γ₂) [ValuationExtension v v₁] [ValuationExtension v v₂] : v₁.IsEquiv v₂ := sorry

-- need more conditions
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {ΓK ΓL: Type*} [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL] (vK : Valuation K ΓK) (vL : Valuation L ΓL) [ValuationExtension vK vL]

theorem Valuation.preserveValuation_of_finiteDimensional_algebra_hom  (s : L →ₐ[K] L) : PreserveValuation vL vL s := sorry
-- vL.IsEquiv (vL.comap s) := sorry
-- (s : L ≃ₐ[K] L)

def AlgHom.liftValuationInteger (s : L →ₐ[K] L) : 𝒪[vL] →ₐ[𝒪[vK]] 𝒪[vL] := sorry

def AlgEquiv.liftValuationInteger (s : L ≃ₐ[K] L) : 𝒪[vL] ≃ₐ[𝒪[vK]] 𝒪[vL] := sorry

-- `If preserve valuation is a class, this AlgHom.liftValuationInteger should be make into a Coe instance`

--def AlgHom.liftValuationIntegerQuotientleIdeal (s : L →ₐ[K] L) (γ : ΓL) : 𝒪[vL]⧸(vL.leIdeal γ) →ₐ[𝒪[vK]] 𝒪[vL]⧸(vL.leIdeal γ) := sorry

--def AlgEquiv.liftValuationIntegerQuotientleIdeal (s : L ≃ₐ[K] L) (γ : ΓL) : (𝒪[vL]⧸(vL.leIdeal γ)) ≃ₐ[𝒪[vK]] (𝒪[vL]⧸(vL.leIdeal γ)) := sorry

-- `LT version`

def AlgHom.liftResidueField (s : L →ₐ[K] L) : 𝓀[vL] →ₐ[𝓀[vK]] 𝓀[vL] := sorry

def AlgEquiv.liftResidueField (s : L ≃ₐ[K] L) : 𝓀[vL] ≃ₐ[𝓀[vK]] 𝓀[vL] := sorry
