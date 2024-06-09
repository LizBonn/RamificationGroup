/-
normalize to `integer` or `valuationSubring`?
-/

import RamificationGroup.Valued.Hom.ValExtension
import LocalClassFieldTheory.DiscreteValuationRing.Extensions
import RamificationGroup.Valuation.Discrete


open Valuation Valued DiscreteValuation

section non_discrete

open Polynomial

namespace Valuation

theorem isEquiv_iff_integer {K : Type*} [DivisionRing K] {Γ₀ Γ'₀ : outParam Type*} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ'₀] (v : Valuation K Γ₀) (v' : Valuation K Γ'₀) :
  v.IsEquiv v' ↔ v.integer = v'.integer := by
  rw [isEquiv_iff_val_le_one]
  constructor <;> intro h
  · ext x; rw [mem_integer_iff, mem_integer_iff]
    exact h
  · intro x
    rw [← mem_integer_iff, ← mem_integer_iff]
    simp only [h]

variable {K L : Type*} {ΓK ΓL: outParam Type*} [Field K] [Field L]
  [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]
  [vK : Valued K ΓK] {v : Valuation L ΓL}
  [Algebra K L] [FiniteDimensional K L]
-- variable [HenselianLocalRing vK.valuationSubring]

theorem eval_lt_one_of_coeff_le_one_of_const_eq_zero_of_lt_one {f : L[X]}
    (hf : ∀n : ℕ, v (f.coeff n) ≤ 1) (h0 : f.coeff 0 = 0)
    {x : L} (hx : v x < 1) :
  v (f.eval x) < 1 := by
  rw [eval_eq_sum_range]
  apply map_sum_lt v (one_ne_zero' ΓL)
  intro n _
  by_cases hn : n = 0
  · rw [hn, h0]
    simp only [pow_zero, mul_one, _root_.map_zero, zero_lt_one]
  · rw [map_mul, map_pow, ← mul_one 1]
    apply mul_lt_mul_of_lt_of_le₀ (hf n) (one_ne_zero) ((pow_lt_one_iff hn).mpr hx)

theorem aeval_valuationSubring_lt_one_of_lt_one
    (h : vK.v.IsEquiv <| v.comap (algebraMap K L))
    (f : 𝒪[K][X]) (h0 : f.coeff 0 = 0) {x : L} (hx : v x < 1) :
  v (aeval x f) < 1 := by
  rw [aeval_def, ← eval_map]
  apply eval_lt_one_of_coeff_le_one_of_const_eq_zero_of_lt_one _ _ hx
  · intro n
    rw [coeff_map, show (algebraMap 𝒪[K] L) (f.coeff n) = (algebraMap K L) (f.coeff n) by rfl, ← comap_apply]
    apply ((isEquiv_iff_val_le_one _ _).mp h).mp (f.coeff n).2
  · simp only [coeff_map, h0, _root_.map_zero]

theorem aeval_valuationSubring_lt_one_of_lt_one_self
  (f : 𝒪[K][X]) (h0 : f.coeff 0 = 0) {x : K} (hx : vK.v x < 1) :
    vK.v (aeval x f) < 1 := by
  rw [aeval_def, ← eval_map]
  apply eval_lt_one_of_coeff_le_one_of_const_eq_zero_of_lt_one _ _ hx
  · intro n
    rw [coeff_map, show (algebraMap 𝒪[K] K) (f.coeff n) = (algebraMap K K) (f.coeff n) by rfl, ← comap_apply]
    apply (f.coeff n).2
  · simp only [coeff_map, h0, _root_.map_zero]

theorem mem_integer_of_mem_integral_closure (h : vK.v.IsEquiv <| v.comap (algebraMap K L))
    {x : L} (hx : x ∈ integralClosure vK.valuationSubring L) :
  x ∈ v.integer := by
  rcases hx with ⟨p, hp⟩
  rw [mem_integer_iff]
  by_contra! vxgt1
  have xne0 : x ≠ 0 := (Valuation.ne_zero_iff v).mp <| ne_of_gt <| lt_trans (zero_lt_one' _) vxgt1
  letI : Invertible x := invertibleOfNonzero xne0
  have : v (aeval x⁻¹ (p.reverse - 1)) < 1 := by
    apply aeval_valuationSubring_lt_one_of_lt_one h
    · simp only [coeff_sub, coeff_zero_reverse, hp.1, Monic.leadingCoeff, coeff_one_zero, sub_self]
    · apply (one_lt_val_iff v xne0).mp vxgt1
  apply ne_of_lt this
  have : aeval x⁻¹ (p.reverse - 1) = -1 := by
    rw [← add_neg_eq_zero]
    ring_nf
    simp only [_root_.map_add, _root_.map_neg, _root_.map_one, add_neg_cancel_left]
    rw [← invOf_eq_inv x, aeval_def, Polynomial.eval₂_reverse_eq_zero_iff, hp.2]
  rw [this, map_neg, map_one]

end Valuation

end non_discrete

variable {K : Type*} [Field K] [vK : Valued K ℤₘ₀]
variable {L : Type*} [Field L]

namespace DiscreteValuation

variable [Algebra K L] [FiniteDimensional K L]

section int_closure_discrete

variable [IsDiscrete vK.v] [CompleteSpace K]
variable {vL : Valuation L ℤₘ₀}

theorem nontrivial_of_valuation_extension (h : vK.v.IsEquiv <| vL.comap (algebraMap K L)) : vL.Nontrivial := by
  rcases exists_Uniformizer_ofDiscrete vK.v with ⟨π, hp⟩
  use (algebraMap K L) π
  constructor
  · rw [← comap_apply, ← IsEquiv.ne_zero h, hp]
    decide
  · apply ne_of_lt
    rw [← comap_apply, ← (isEquiv_iff_val_lt_one _ _).mp h, hp]
    decide

/-- If a valuation `v : L → ℤₘ₀` extends a discrete valuation on `K`, then `v` is equivalent to `extendedValuation K L`.-/
theorem extension_valuation_equiv_extendedValuation_of_discrete
  (h : vK.v.IsEquiv <| vL.comap (algebraMap K L)) :
    vL.IsEquiv (extendedValuation K L) := by
  letI : vL.Nontrivial := nontrivial_of_valuation_extension h
  apply IsEquiv.trans (isEquiv_ofNontrivial vL) (isEquiv_of_le_one_le_one _).symm
  intro x
  rw [← mem_valuationSubring_iff, ← ValuationSubring.mem_toSubring, ← Extension.integralClosure_eq_integer, ← (isEquiv_iff_val_le_one _ _).mp (isEquiv_ofNontrivial vL)]
  apply mem_integer_of_mem_integral_closure h

theorem extension_integer_eq_extendedValuation_of_discrete (h : vK.v.IsEquiv <| vL.comap (algebraMap K L)) :
  vL.integer = (extendedValuation K L).integer := by
  rw [← isEquiv_iff_integer]
  exact extension_valuation_equiv_extendedValuation_of_discrete h

theorem integral_closure_eq_integer_of_complete_discrete
    (h : vK.v.IsEquiv <| vL.comap (algebraMap K L)) :
  (integralClosure vK.valuationSubring L).toSubring = vL.integer := by
  rw [Extension.integralClosure_eq_integer, extension_integer_eq_extendedValuation_of_discrete h]
  ext
  rw [ValuationSubring.mem_toSubring, mem_valuationSubring_iff, mem_integer_iff]

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

theorem unique_val_of_ext
  (h₁ : vK.v.IsEquiv <| v₁.comap (algebraMap K L))
  (h₂ : vK.v.IsEquiv <| v₂.comap (algebraMap K L)) :
    v₁.IsEquiv v₂ :=
  (Valuation.isEquiv_iff_valuationSubring _ _).mpr <| unique_valuationSubring_of_ext h₁ h₂

end value_ext

end DiscreteValuation

namespace DiscreteValuation

variable [CompleteSpace K] [IsDiscrete vK.v] [vL : Valued L ℤₘ₀]
variable [Algebra K L] [IsValExtension K L] [FiniteDimensional K L]

theorem algHom_preserve_val_of_complete (f : L →ₐ[K] L) : vL.v.IsEquiv <| vL.v.comap f := by
  apply unique_val_of_ext (K := K)
  · apply IsValExtension.val_isEquiv_comap
  · rw [Valuation.isEquiv_iff_val_le_one]
    simp only [comap_apply, RingHom.coe_coe, AlgHom.commutes]
    intro x
    rw [← Valuation.comap_apply (algebraMap K L)]
    revert x
    rw [← Valuation.isEquiv_iff_val_le_one]
    apply IsValExtension.val_isEquiv_comap

theorem algEquiv_preserve_val_of_complete (f : L ≃ₐ[K] L) : vL.v.IsEquiv <| vL.v.comap f := algHom_preserve_val_of_complete f.toAlgHom

/-
-- `should be changed into G_-1 = Top, into a later file`
variable (K L) in
def fromAlgEquiv : (L ≃ₐ[K] L) →* (L ≃ₐv[K] L) where
  toFun := fun f ↦ mk' f <| algEquiv_preserve_val f
  map_one' := rfl
  map_mul' := sorry

variable (K L) in
def equivAlgEquiv : (L ≃ₐ[K] L) ≃* (L ≃ₐv[K] L) := {
  fromAlgEquiv K L with
  invFun := toAlgEquiv
  left_inv := sorry
  right_inv := sorry
}
-/

end DiscreteValuation
