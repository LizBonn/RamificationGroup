import LocalClassFieldTheory.DiscreteValuationRing.Basic

open Valuation DiscreteValuation

section check
variable {K} [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [vK : Valued K ℤₘ₀]

#check [IsDiscrete vK.v] -- use this for discrete valuation

#check Valuation.valuationSubring -- use this for `𝒪[K]`
#check Valuation.integer -- only subring, do not need K to be a field

end check

namespace Valued

instance preorder {R : Type*} {Γ : outParam Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ] [Valued R Γ]: Preorder R := Preorder.lift Valued.v

/-- An abbrevation for `Valuation.valuationSubring` of a `Valued` instance, it serves for notation `𝒪[K]` -/
@[reducible]
def valuationSubring (K : Type*) [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] : ValuationSubring K := (Valued.v).valuationSubring

scoped notation:max " 𝒪[" K:max "] " => Valued.valuationSubring K

variable (R K : Type*) [Ring R] [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [vR : Valued R Γ] [vK : Valued K Γ]

-- is this instance OK?
instance integer.valued: Valued vR.v.integer Γ := Valued.mk' (vR.v.comap vR.v.integer.subtype)

-- need to add this, lean cannot infer this
-- `This will be fixed if Valuation.valuationSubring is with @[reducible] tag`, for now, every instance need to be written again for `𝒪[K]`
instance valuationSubring.valued: Valued 𝒪[K] Γ := inferInstanceAs (Valued vK.v.integer Γ)

#synth Valued 𝒪[K] Γ
#synth LocalRing 𝒪[K]
#synth Algebra 𝒪[K] K

/- -- For `Valued.liftInteger`
theorem integer_valuation_eq : (Valued.integer.valued R).v = (vR.v.comap vR.v.integer.subtype) := rfl

theorem integerAlgebraMap.monotone : Monotone (algebraMap 𝒪[K] K) := sorry

-- also value IsEquiv of O[K] and K -- they are equal!
-- `First show val is equiv, then use theorem IsEquiv implies monotone and continuous!!!!!`
-/

/-- An abbrevation for `LocalRing.maximalIdeal 𝒪[K]` of a `Valued` instance, it serves for notation `𝓂[K]` -/
@[reducible]
def maximalIdeal (K : Type*) [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] : Ideal 𝒪[K] := LocalRing.maximalIdeal 𝒪[K]

scoped notation:max " 𝓂[" K:max "] " => maximalIdeal K

#synth 𝓂[K].IsMaximal

/-
theorem maximalIdeal_eq {K : Type*} [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] : 𝓂[K] = (Valued.v).ltIdeal 1 := sorry
-/

/-- An abbrevation for `LocalRing.ResidueField 𝒪[K]` of a `Valued` instance, it serves for notation `𝓀[K]` -/
@[reducible]
def ResidueField (K : Type*) [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] := LocalRing.ResidueField (𝒪[K])

scoped notation:max " 𝓀[" K:max "] " => ResidueField K

/- -- is this needed?
instance valuationSubring.coeResidueField {K : Type*} {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Field K] [Valued K Γ] : Coe 𝒪[K] 𝓀[K] where
  coe := LocalRing.residue 𝒪[K]
-/

end Valued
