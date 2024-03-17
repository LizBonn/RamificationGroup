import RamificationGroup.Valued.Basic

open Valuation DiscreteValuation Valued

instance integerDiscreteValuationRing {K : Type*} [Field K] [Valued K ℤₘ₀]: DiscreteValuationRing 𝒪[K] := sorry

-- `theorem: if two discrete valuations are equivalent, then they are equal`
