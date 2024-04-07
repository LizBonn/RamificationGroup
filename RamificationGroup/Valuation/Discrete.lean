import LocalClassFieldTheory.DiscreteValuationRing.Complete
import LocalClassFieldTheory.DiscreteValuationRing.DiscreteNorm
import RamificationGroup.ForMathlib.Henselian
import RamificationGroup.Valued.Defs



open Valuation Valued DiscreteValuation

#check IsRankOne
#check IsDiscrete
#check DiscreteValuation.isRankOne


section approximation

namespace DiscreteValuation

open IsRankOne
open scoped NNReal

variable {K : Type*} [Field K]
  -- {ΓK ΓK' : outParam Type*}
  -- [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓK']
  -- {v₁ : Valuation K ΓK} [IsRankOne v₁]
  -- {v' : Valuation K ΓK'} [IsRankOne v']
  {v v' : Valuation K ℤₘ₀} [IsDiscrete v] [IsDiscrete v']

-- theorem isEquiv_iff_eq_pow : v.IsEquiv v' ↔ ∃s : ℝ≥0, ∀x : K, hom v (v x) = ((hom v' (v' x)) ^ (s : Real)) := by
--   sorry

-- #check pow_Uniformizer
-- theorem val_pow_Uniformizer : sorry := sorry

theorem isEquiv_of_le_one_le_one_of_eq_one_eq_one
    (h : ∀x : K, v x ≤ 1 → v' x ≤ 1) (h1 : ∀x : K, v x = 1 → v' x = 1) :
  v.IsEquiv v' := by
  sorry

theorem isEquiv_of_le_one_le_one (h : ∀x : K, v x ≤ 1 → v' x ≤ 1) :
  v.IsEquiv v' := by
  -- rcases exists_Uniformizer_ofDiscrete v with ⟨π, hπ⟩

  sorry


end DiscreteValuation

end approximation


section adic_complete

variable {K : Type*} [Field K] [vK : Valued K ℤₘ₀]

local notation "m[" K "]" => LocalRing.maximalIdeal 𝒪[K]

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
