/-
-/

import RamificationGroup.Valued.Hom.Defs
import LocalClassFieldTheory.DiscreteValuationRing.Extensions
import RamificationGroup.ForMathlib.Henselian

open Valuation Valued DiscreteValuation

section hensel

variable {K L : Type*} {ΓK ΓL: outParam Type*} [Field K] [Field L]
  [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]
  [vK : Valued K ΓK] {v : Valuation L ΓL}
  [Algebra K L] [FiniteDimensional K L]

theorem integral_closure_eq_integer_of_henselian [HenselianLocalRing vK.valuationSubring]
  (h : vK.v.IsEquiv <| v.comap (algebraMap K L)) :
    (integralClosure vK.v.valuationSubring L).toSubring = v.integer := by
  sorry


end hensel

variable {K : Type*} [Field K] [vK : Valued K ℤₘ₀]
variable {L : Type*} [Field L]

namespace DiscreteValuation

variable [Algebra K L] [FiniteDimensional K L]

section int_closure_discrete

variable {v : Valuation L ℤₘ₀}

variable (K) in
instance instIsAdicCompleteToCompleteToDiscrete [CompleteSpace K] [IsDiscrete vK.v] : IsAdicComplete (LocalRing.maximalIdeal 𝒪[K]) 𝒪[K] := by
  sorry

variable (K) in
instance instHenselianToCompleteToDiscrete [CompleteSpace K] [IsDiscrete vK.v] :
  HenselianLocalRing vK.valuationSubring := inferInstance

theorem integral_closure_eq_integer_of_complete_discrete [CompleteSpace K] [IsDiscrete vK.v]
  (h : vK.v.IsEquiv <| v.comap (algebraMap K L)) :
    (integralClosure vK.v.valuationSubring L).toSubring = v.integer := integral_closure_eq_integer_of_henselian h

end int_closure_discrete

section value_ext

variable [CompleteSpace K] [IsDiscrete vK.v]
variable {v₁ v₂ : Valuation L ℤₘ₀}

theorem unique_valuationSubring_of_ext (h₁ : vK.v.IsEquiv <| v₁.comap (algebraMap K L))
  (h₂ : vK.v.IsEquiv <| v₂.comap (algebraMap K L)) :
    v₁.valuationSubring = v₂.valuationSubring := by
  ext
  rw [Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff,
    ← Valuation.mem_integer_iff, ← Valuation.mem_integer_iff,
    ← integral_closure_eq_integer_of_complete_discrete h₁, ← integral_closure_eq_integer_of_complete_discrete h₂]

theorem unique_val_of_ext (h₁ : vK.v.IsEquiv <| v₁.comap (algebraMap K L))
  (h₂ : vK.v.IsEquiv <| v₂.comap (algebraMap K L)) :
    v₁.IsEquiv v₂ :=
  (Valuation.isEquiv_iff_valuationSubring _ _).mpr <| unique_valuationSubring_of_ext h₁ h₂

end value_ext

end DiscreteValuation

namespace ValAlgEquiv

open DiscreteValuation

variable [CompleteSpace K] [IsDiscrete vK.v] [vL : Valued L ℤₘ₀]
variable [ValAlgebra K L] [FiniteDimensional K L] [CompleteSpace K]

theorem algEnd_preserve_val (f : L →ₐ[K] L) : vL.v.IsEquiv <| vL.v.comap f := by
  apply unique_val_of_ext (K := K)
  · apply ValAlgebra.val_isEquiv_comap
  · rw [Valuation.isEquiv_iff_val_le_one]
    simp only [comap_apply, RingHom.coe_coe, AlgHom.commutes]
    intro x
    rw [← Valuation.comap_apply (algebraMap K L)]
    revert x
    rw [← Valuation.isEquiv_iff_val_le_one]
    apply ValAlgebra.val_isEquiv_comap

theorem algEquiv_preserve_val (f : L ≃ₐ[K] L) : vL.v.IsEquiv <| vL.v.comap f := algEnd_preserve_val f.toAlgHom

variable (K L) in
def fromAlgEquiv : (L ≃ₐ[K] L) →* (L ≃ₐv[K] L) where
  toFun := fun f ↦ mk' f <| algEquiv_preserve_val f
  map_one' := rfl
  map_mul' := sorry

variable (K L) in
def equivAlgEquiv : (L ≃ₐ[K] L) ≃* (L ≃ₐv[K] L) where
  toFun := fromAlgEquiv K L
  invFun := toAlgEquiv
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry

end ValAlgEquiv
