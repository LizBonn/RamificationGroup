import RamificationGroup.Valuation.Integer
import Mathlib.Topology.Algebra.Valuation
import Mathlib.RingTheory.DiscreteValuationRing.Basic

open DiscreteValuation

section DiscretelyValued

class DiscretelyValued (R : Type*) [Ring R] extends Valued R ℤₘ₀ where
  -- v_is_surj : (v.toFun).Surjective
  /- This `v_is_surj` is the same as Maria and Phillip's is_discrete -/
  exist_val_one : ∃ x : R, Valued.v x = 1

class CompleteDiscretelyValued (R : Type*) [Ring R] extends DiscretelyValued R, CompleteSpace R

end DiscretelyValued

section DVF

namespace DiscretelyValued

-- this def is the same as `Valuation.integer`, it only serves for notation `𝒪[K]`
abbrev integer (K : Type*) [Field K] [DiscretelyValued K] : Subring K := (Valued.v).integer

scoped notation:max " 𝒪[" K:max "] " => DiscretelyValued.integer K

instance {K : Type*} [Field K] [DiscretelyValued K]: DiscretelyValued 𝒪[K] := sorry

instance {K : Type*} [Field K] [DiscretelyValued K]: DiscreteValuationRing 𝒪[K] := sorry

abbrev maximalIdeal (K : Type*) [Field K] [DiscretelyValued K] : Ideal 𝒪[K] := (Valued.v).LTIdeal 1

scoped notation:max " 𝓂[" K:max "] " => maximalIdeal K

theorem maximalIdeal_eq {K : Type*} [Field K] [DiscretelyValued K] : 𝓂[K] = LocalRing.maximalIdeal 𝒪[K] := sorry

instance {K : Type*} [Field K] [DiscretelyValued K] : Ideal.IsMaximal 𝓂[K] := maximalIdeal_eq (K := K) ▸ inferInstance

/- `Alternative definition of 𝒪[K]`
abbrev maximalIdeal (K : Type*) [Field K] [DiscretelyValued K] : Ideal 𝒪[K] := LocalRing.maximalIdeal 𝒪[K]

scoped notation:max " 𝓂[" K:max "] " => maximalIdeal K

theorem xxx {K : Type*} [Field K] [DiscretelyValued K] : 𝓂[K] = (Valued.v).LTIdeal 1 := sorry

instance {K : Type*} [Field K] [DiscretelyValued K] : Ideal.IsMaximal ((Valued.v).LTIdeal (1:ℤₘ₀) : Ideal 𝒪[K]) := DiscretelyValued.xxx (K := K) ▸ inferInstance
-/

scoped notation:max " 𝓀[" K:max "] " => LocalRing.ResidueField (𝒪[K])

def integerQuotientMaximalIdealEquiv {K : Type*} [Field K] [DiscretelyValued K] : (𝒪[K] ⧸ 𝓂[K]) ≃ₐ[𝒪[K]] 𝓀[K] := Ideal.quotientEquivAlgOfEq 𝒪[K] maximalIdeal_eq

instance {K : Type*} [Field K] [DiscretelyValued K] : Coe 𝒪[K] 𝓀[K] where
  coe := LocalRing.residue 𝒪[K]

end DiscretelyValued
end DVF
