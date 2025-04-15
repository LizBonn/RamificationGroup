-- Cannot complie (2025/4/14)
import RamificationGroup.Valued.Basic

open Valuation DiscreteValuation Valued

/--
Haven't been used (2025/4/14)-/
instance integerDiscreteValuationRing {K : Type*} [Field K] [Valued K ℤₘ₀]: DiscreteValuationRing 𝒪[K] := sorry

-- `theorem: if two discrete valuations are equivalent, then they are equal`
