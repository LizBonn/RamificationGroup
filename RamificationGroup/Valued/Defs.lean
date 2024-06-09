import Mathlib.Topology.Algebra.Valuation

namespace Valued

/-- A `Valued` version of `Valuation.valuationSubring`, enabling the notation `𝒪[K]` for valued field `K` -/
@[reducible]
def valuationSubring (K : Type*) [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] : ValuationSubring K := (Valued.v).valuationSubring

@[inherit_doc]
scoped notation "𝒪[" K "]" => Valued.valuationSubring K

/-- An abbrevation for `LocalRing.maximalIdeal 𝒪[K]` of a valued field `K`, enabling the notation `𝓂[K]` -/
@[reducible]
def maximalIdeal (K : Type*) [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] : Ideal 𝒪[K] := LocalRing.maximalIdeal 𝒪[K]

@[inherit_doc]
scoped notation "𝓂[" K "]" => maximalIdeal K

/-- An abbrevation for `LocalRing.ResidueField 𝒪[K]` of a `Valued` instance, enabling the notation `𝓀[K]` -/
@[reducible]
def ResidueField (K : Type*) [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] := LocalRing.ResidueField (𝒪[K])

@[inherit_doc]
scoped notation:max "𝓀[" K:max "]" => ResidueField K

end Valued

/-

section IntegerValued
variable (R K : Type*) [Ring R] [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [vR : Valued R Γ] [vK : Valued K Γ]

--`Is this really needed now? when there is no need for ValHom`
-- is this instance OK? or is it needed? If needed add simp lemmas saying `v (s.liftInteger x) = v (s x.val) `
instance integer.valued: Valued vR.v.integer Γ := Valued.mk' (vR.v.comap vR.v.integer.subtype)


-- need to add this, lean cannot infer this
-- `This will be auto infered once Valuation.valuationSubring is with @[reducible] tag or at least @[instance]`, for now, every instance need to be written again for `𝒪[K]`, in this file and Hom.lift file and more. This is also the reason that valuationSubring should with tag @[reducible]. Add this tag to `Valuation.valuationSubring` when impoet to mathlib!
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

/-
theorem maximalIdeal_eq {K : Type*} [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] : 𝓂[K] = (Valued.v).ltIdeal 1 := sorry
-/



-- TODO? : Should residue field be equipped with trivial valuation?
-- A generalization of this could be : after a valued ring quotient a "upper-closed" value ideal, it is equipped with a quotient valuation
