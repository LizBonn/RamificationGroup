/-
# of WARNINGs : 1
-/

import RamificationGroup.Valued.Hom.Defs
import LocalClassFieldTheory.DiscreteValuationRing.Extensions
import RamificationGroup.ForMathlib.Henselian

variable {K : Type*} {ΓK : outParam Type*} [Field K]
  [LinearOrderedCommGroupWithZero ΓK] [vK : Valued K ΓK]
variable {L : Type*} [Field L]

namespace Valuation

variable [Algebra K L] [FiniteDimensional K L]

section int_closure

variable {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ]
  {v : Valuation L Γ}

theorem integral_closure_eq_integer_of_helselian [HenselianLocalRing vK.valuationSubring]
  (h : vK.v.IsEquiv <| v.comap (algebraMap K L)) :
    (integralClosure vK.v.valuationSubring L).toSubring = v.integer := by
  sorry

/-- WARNING : not mathematically true? more conditions? -/
instance ___false___HenselianOfComplete [CompleteSpace K] : HenselianLocalRing vK.valuationSubring := by
  sorry

theorem integral_closure_eq_integer_of_complete_of_ext [CompleteSpace K]
  (h : vK.v.IsEquiv <| v.comap (algebraMap K L)) :
    (integralClosure vK.v.valuationSubring L).toSubring = v.integer := by
  sorry

end int_closure

section value_ext

variable [CompleteSpace K]
variable {Γ₁ Γ₂ : outParam Type*} [LinearOrderedCommGroupWithZero Γ₁] [LinearOrderedCommGroupWithZero Γ₂]
  {v₁ : Valuation L Γ₁} {v₂ : Valuation L Γ₂}

theorem unique_valuationSubring_of_ext (h₁ : vK.v.IsEquiv <| v₁.comap (algebraMap K L))
  (h₂ : vK.v.IsEquiv <| v₂.comap (algebraMap K L)) :
    v₁.valuationSubring = v₂.valuationSubring := by
  ext
  rw [Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff,
    ← Valuation.mem_integer_iff, ← Valuation.mem_integer_iff,
    ← integral_closure_eq_integer_of_complete_of_ext h₁, ← integral_closure_eq_integer_of_complete_of_ext h₂]

theorem unique_val_of_ext (h₁ : vK.v.IsEquiv <| v₁.comap (algebraMap K L))
  (h₂ : vK.v.IsEquiv <| v₂.comap (algebraMap K L)) :
    v₁.IsEquiv v₂ :=
  (Valuation.isEquiv_iff_valuationSubring _ _).mpr <| unique_valuationSubring_of_ext h₁ h₂


end value_ext

end Valuation

namespace ValAlgEquiv

section alg_end
variable {ΓL : outParam Type*} [LinearOrderedCommGroupWithZero ΓL] [vL : Valued L ΓL]
variable [ValAlgebra K L] [FiniteDimensional K L] [CompleteSpace K]

theorem algEnd_preserve_val (f : L →ₐ[K] L) : vL.v.IsEquiv <| vL.v.comap f := by
  apply Valuation.unique_val_of_ext (K := K)
  · apply ValAlgebra.val_isEquiv_comap
  · rw [Valuation.isEquiv_iff_val_le_one]
    simp; intro x
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

end alg_end

end ValAlgEquiv
