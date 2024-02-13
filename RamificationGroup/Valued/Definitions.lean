import RamificationGroup.Valuation.Integer
import Mathlib.Topology.Algebra.Valuation
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.ValuationRing

open DiscreteValuation

section DiscretelyValued

class DiscretelyValued (R : Type*) [Ring R] extends Valued R ℤₘ₀ where
  -- v_is_surj : (v.toFun).Surjective
  /- This `v_is_surj` is the same as Maria and Phillip's is_discrete -/
  exist_val_one : ∃ x : R, Valued.v x = ofZ 1
  /- Is this definition OK? Wait for the theorems to decide -/

class CompleteDiscretelyValued (R : Type*) [Ring R] extends DiscretelyValued R, CompleteSpace R

end DiscretelyValued


section DVF

namespace Valued
-- this def is the same as `Valuation.integer`, it only serves for notation `𝒪[K]`
abbrev integer (K : Type*) [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] : Subring K := (Valued.v).integer

scoped notation:max " 𝒪[" K:max "] " => Valued.integer K

instance (K : Type*) [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] : Valued 𝒪[K] Γ := sorry

-- Is this instance OK? Is it possible for K has many Valued instance for different Γ?
def integerValuationRing (K : Type*) [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] : ValuationRing 𝒪[K] := sorry

abbrev maximalIdeal (K : Type*) [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] : Ideal 𝒪[K] := (Valued.v).LTIdeal 1

scoped notation:max " 𝓂[" K:max "] " => maximalIdeal K

theorem maximalIdeal_eq {K : Type*} [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] : 𝓂[K] = @LocalRing.maximalIdeal 𝒪[K] _ ((integerValuationRing K).localRing) := sorry

instance {K : Type*} [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] : Ideal.IsMaximal 𝓂[K] := maximalIdeal_eq (K := K) ▸ inferInstance

abbrev residueField (K : Type*) [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] := @LocalRing.ResidueField (𝒪[K]) _ (@ValuationRing.localRing _ _ _ (integerValuationRing K))

scoped notation:max " 𝓀[" K:max "] " => residueField K

def integerQuotientMaximalIdealEquiv {K : Type*} [Field K] [DiscretelyValued K] : (𝒪[K] ⧸ 𝓂[K]) ≃ₐ[𝒪[K]] 𝓀[K] := Ideal.quotientEquivAlgOfEq 𝒪[K] maximalIdeal_eq

instance {K : Type*} [Field K] [DiscretelyValued K] : Coe 𝒪[K] 𝓀[K] where
  coe := @LocalRing.residue 𝒪[K] _ (@ValuationRing.localRing _ _ _ (integerValuationRing K))

end Valued

open Valued

namespace DiscretelyValued

instance {K : Type*} [Field K] [DiscretelyValued K]: DiscretelyValued 𝒪[K] := sorry

instance {K : Type*} [Field K] [DiscretelyValued K]: DiscreteValuationRing 𝒪[K] := sorry



/- `Alternative definition of 𝓂[K]`
abbrev maximalIdeal (K : Type*) [Field K] [DiscretelyValued K] : Ideal 𝒪[K] := LocalRing.maximalIdeal 𝒪[K]

scoped notation:max " 𝓂[" K:max "] " => maximalIdeal K

theorem xxx {K : Type*} [Field K] [DiscretelyValued K] : 𝓂[K] = (Valued.v).LTIdeal 1 := sorry

instance {K : Type*} [Field K] [DiscretelyValued K] : Ideal.IsMaximal ((Valued.v).LTIdeal (1:ℤₘ₀) : Ideal 𝒪[K]) := DiscretelyValued.xxx (K := K) ▸ inferInstance
-/

end DiscretelyValued

-- `theorem: if two discrete valuations are equivalent, then they are equal`

end DVF
