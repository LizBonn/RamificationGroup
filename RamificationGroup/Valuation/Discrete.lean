import LocalClassFieldTheory.DiscreteValuationRing.Complete
import LocalClassFieldTheory.DiscreteValuationRing.DiscreteNorm
import RamificationGroup.ForMathlib.Henselian
import RamificationGroup.Valued.Hom.Defs

#check Valued.mem_nhds_zero

open Valuation Valued DiscreteValuation

variable {K : Type*} [Field K] [vK : Valued K ℤₘ₀]

local notation "m[" K "]" => LocalRing.maximalIdeal 𝒪[K]

namespace DiscreteValuation

#synth IsFractionRing 𝒪[K] K

section adic_complete

variable [CompleteSpace K] [IsDiscrete vK.v]

variable (K)

theorem isHausdorff_of_complete_of_discrete [CompleteSpace K] [IsDiscrete vK.v] : IsHausdorff m[K] 𝒪[K] where
  haus' := by
    sorry

instance instIsAdicCompleteToCompleteToDiscrete [CompleteSpace K] [IsDiscrete vK.v] : IsAdicComplete (LocalRing.maximalIdeal 𝒪[K]) 𝒪[K] := by
  sorry

instance instHenselianLocalRingToCompleteToDiscrete :
  HenselianLocalRing vK.valuationSubring := inferInstance

end adic_complete
