import LocalClassFieldTheory.DiscreteValuationRing.Basic

open Valuation DiscreteValuation

section check
variable {K} [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [vK : Valued K ℤₘ₀]

#check [IsDiscrete vK.v] -- use this for discrete valuation

#check Valuation.valuationSubring -- use this for `𝒪[K]`
#check Valuation.integer -- only subring, do not need K to be a field

end check

namespace Valued


/-

section Preorder

variable {R : Type*} {Γ : outParam Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ] [Valued R Γ]

-- the preoder lift from valuation is different from the proorder of divisibility -- there is a preorder on the valuations, called specialization?
instance preorder : Preorder R := Valuation.toPreorder Valued.v

theorem le_iff_val_le (x y : R) : x ≤ y ↔ v x ≤ v y := sorry

theorem lt_iff_val_lt (x y : R) : x < y ↔ v x < v y := sorry

theorem le_one_iff_val_le_one (x y : R) : x ≤ 1 ↔ v x ≤ 1 := sorry

theorem lt_one_iff_val_lt_one (x y : R) : x < 1 ↔ v x < 1 := sorry

theorem zero_le (x y : R) : 0 ≤ x := sorry

-- lower TODO : `theorems that x + y ≤ x, x + y < x,...`

end Preorder

-/


/-- An `Valued` version of `Valuation.valuationSubring`, it serves for the notation `𝒪[K]` -/
@[reducible]
def valuationSubring (K : Type*) [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] : ValuationSubring K := (Valued.v).valuationSubring

scoped notation:max "𝒪[" K:max "]" => Valued.valuationSubring K

/-

section IntegerValued
variable (R K : Type*) [Ring R] [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [vR : Valued R Γ] [vK : Valued K Γ]

--`Is this really needed now? when there is no need for ValHom`
-- is this instance OK? or is it needed? If needed add simp lemmas saying `v (s.liftInteger x) = v (s x.val) `
instance integer.valued: Valued vR.v.integer Γ := Valued.mk' (vR.v.comap vR.v.integer.subtype)


-- need to add this, lean cannot infer this
-- `This will be auto infered once Valuation.valuationSubring is with @[reducible] tag`, for now, every instance need to be written again for `𝒪[K]`, in this file and Hom.lift file and more. This is also the reason that valuationSubring should with tag @[reducible]. Add this tag to `Valuation.valuationSubring` when impoet to mathlib!
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

@[simp]
theorem integer_val_coe (x : vR.v.integer) : Valued.v x = Valued.v (x : R) := rfl

@[simp]
theorem valuationSubring_val_coe (x : 𝒪[K]): v x = v (x : K) := rfl

theorem integer_val_le_one (x : vR.v.integer) : Valued.v x ≤ 1 := (mem_integer_iff vR.v x.1).mp x.2

#check mem_integer_iff

end IntegerValued

-/

-- `theorems about the relation between order and valuation?`

/-- An abbrevation for `LocalRing.maximalIdeal 𝒪[K]` of a `Valued` instance, it serves for notation `𝓂[K]` -/
@[reducible]
def maximalIdeal (K : Type*) [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] : Ideal 𝒪[K] := LocalRing.maximalIdeal 𝒪[K]

scoped notation:max "𝓂[" K:max "]" => maximalIdeal K

/-
theorem maximalIdeal_eq {K : Type*} [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] : 𝓂[K] = (Valued.v).ltIdeal 1 := sorry
-/

/-- An abbrevation for `LocalRing.ResidueField 𝒪[K]` of a `Valued` instance, it serves for notation `𝓀[K]` -/
@[reducible]
def ResidueField (K : Type*) [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] := LocalRing.ResidueField (𝒪[K])

scoped notation:max "𝓀[" K:max "]" => ResidueField K

/- -- is this needed?
instance valuationSubring.coeResidueField {K : Type*} {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Field K] [Valued K Γ] : Coe 𝒪[K] 𝓀[K] where
  coe := LocalRing.residue 𝒪[K]
-/

-- TODO? : Should residue field be equipped with trivial valuation?
-- A generalization of this could be : after a valued ring quotient a "upper-closed" value ideal, it is equipped with a quotient valuation

end Valued
