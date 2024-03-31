import LocalClassFieldTheory.DiscreteValuationRing.Complete
import LocalClassFieldTheory.DiscreteValuationRing.DiscreteNorm
import RamificationGroup.ForMathlib.Henselian
import RamificationGroup.Valued.Hom.Defs



open Valuation Valued DiscreteValuation

variable {K : Type*} [Field K] [vK : Valued K ℤₘ₀]

namespace DiscreteValuation

variable (K) in
instance instIsAdicCompleteToCompleteToDiscrete [CompleteSpace K] [IsDiscrete vK.v] : IsAdicComplete (LocalRing.maximalIdeal 𝒪[K]) 𝒪[K] := by
  sorry

variable (K) in
instance instHenselianToCompleteToDiscrete [CompleteSpace K] [IsDiscrete vK.v] :
  HenselianLocalRing vK.valuationSubring := inferInstance
