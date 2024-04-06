/-
use approximation lemma
normalize to `integer` or `valuationSubring`?
-/

import RamificationGroup.Valued.Hom.Defs
import LocalClassFieldTheory.DiscreteValuationRing.Extensions
import RamificationGroup.Valuation.Discrete


open Valuation Valued DiscreteValuation


section hensel

open Polynomial

namespace Valuation

variable {K L : Type*} {ΓK ΓL: outParam Type*} [Field K] [Field L]
  [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]
  [vK : Valued K ΓK] {v : Valuation L ΓL}
  [Algebra K L] [FiniteDimensional K L]
-- variable [HenselianLocalRing vK.valuationSubring]

#check extendedValuation

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

-- theorem val_coeff_le_val_const_of_irreducible_of_monic {f : K[X]}
--     (h_irr : Irreducible f) (h_monic : f.Monic) (n : ℕ) :
--   vK.v (f.coeff n) ≤ vK.v (f.coeff 0) := by
--   -- have to use Hensel's lemma
--   sorry

-- theorem val_minpoly_coeff_le_val_const_of_integer (x : L) (n : ℕ) : vK.v ((minpoly K x).coeff n) ≤ vK.v ((minpoly K x).coeff 0) := by
--   apply val_coeff_le_val_const_of_irreducible_of_monic (minpoly.irreducible <| IsIntegral.of_finite K x) (minpoly.monic <| IsIntegral.of_finite K x)

-- theorem val_minpoly_const_le_one_of_integer
--     (h : vK.v.IsEquiv <| v.comap (algebraMap K L)) {x : L}
--     (hx : x ∈ v.integer) : vK.v ((minpoly K x).coeff 0) ≤ 1 := by
--   -- have to use Hensel's lemma
--   sorry


-- theorem val_coeff_minpoly_of_integer
--     (h : vK.v.IsEquiv <| v.comap (algebraMap K L)) {x : L}
--     (hx : x ∈ v.integer) (n : ℕ) :
--   (minpoly K x).coeff n ∈ 𝒪[K] := by
--   rw [mem_valuationSubring_iff]
--   apply le_trans (b := vK.v ((minpoly K x).coeff 0))
--   · apply val_minpoly_coeff_le_val_const_of_integer
--   · sorry

-- theorem isIntegral_valuationSubring_of_integer
--     (h : vK.v.IsEquiv <| v.comap (algebraMap K L)) {x : L}
--     (hx : x ∈ v.integer) :
--   IsIntegral 𝒪[K] x := by
--   use intPolynomial vK.v <| val_coeff_minpoly_of_integer h hx
--   constructor
--   · simp only [IntPolynomial.monic_iff]
--     apply minpoly.monic <| IsIntegral.of_finite K x
--   · rw [IntPolynomial.eval₂_eq, minpoly.aeval]

theorem mem_integer_of_mem_integral_closure (h : vK.v.IsEquiv <| v.comap (algebraMap K L))
    {x : L} (hx : x ∈ integralClosure vK.valuationSubring L) :
  x ∈ v.integer := by
  rcases hx with ⟨p, h_monic, h_eval⟩
  rw [mem_integer_iff]
  by_contra! vxgt1
  have xne0 : x ≠ 0 := (Valuation.ne_zero_iff v).mp <| ne_of_gt <| lt_trans (zero_lt_one' _) vxgt1
  letI : Invertible x := invertibleOfNonzero xne0
  let g := p.reverse - 1
  have : v (aeval x⁻¹ g) < 1 := by
    apply aeval_valuationSubring_lt_one_of_lt_one h
    · rw [show g = p.reverse - 1 by rfl]
      simp only [coeff_sub, coeff_zero_reverse, h_monic, Monic.leadingCoeff, coeff_one_zero,
        sub_self]
    · apply (one_lt_val_iff v xne0).mp vxgt1
  apply ne_of_lt this
  have : aeval x⁻¹ g = -1 := by
    rw [← add_neg_eq_zero]
    ring_nf
    simp only [_root_.map_add, _root_.map_neg, _root_.map_one, add_neg_cancel_left]
    rw [← invOf_eq_inv x, aeval_def, Polynomial.eval₂_reverse_eq_zero_iff, h_eval]
  rw [this, map_neg, map_one]

-- theorem eq_integer_of_subset_integer {ΓL' : outParam Type*}
--     [LinearOrderedCommGroupWithZero ΓL'] {v' : Valuation L ΓL'}
--     (h : ∀x : L, x ∈ v.integer → x ∈ v'.integer) :
--   v.integer = v'.integer := by
--   sorry

theorem eq_integer_of_subset_integer {ΓL' : outParam Type*}
    [LinearOrderedCommGroupWithZero ΓL'] {v' : Valuation L ΓL'}
    (h : ∀x : L, x ∈ v.integer → x ∈ v'.integer) :
  v.integer = v'.integer := by
  -- use approximation lemma
  sorry

end Valuation

end hensel

variable {K : Type*} [Field K] [vK : Valued K ℤₘ₀]
variable {L : Type*} [Field L]

namespace DiscreteValuation

variable [Algebra K L] [FiniteDimensional K L]

section int_closure_discrete

variable [IsDiscrete vK.v] [CompleteSpace K]
variable {v : Valuation L ℤₘ₀}

#check extendedValuation K L

theorem aux0 (h : vK.v.IsEquiv <| v.comap (algebraMap K L)) :
  v.integer = (extendedValuation K L).integer := by
  apply Eq.symm
  apply eq_integer_of_subset_integer
  intro x
  rw [mem_integer_iff, ← mem_valuationSubring_iff, ← ValuationSubring.mem_toSubring,
    ← Extension.integralClosure_eq_integer]
  apply mem_integer_of_mem_integral_closure h

theorem integral_closure_eq_integer_of_complete_discrete
    (h : vK.v.IsEquiv <| v.comap (algebraMap K L)) :
  (integralClosure vK.valuationSubring L).toSubring = v.integer := by
  rw [Extension.integralClosure_eq_integer, aux0 h]
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

theorem unique_val_of_ext (h₁ : vK.v.IsEquiv <| v₁.comap (algebraMap K L))
  (h₂ : vK.v.IsEquiv <| v₂.comap (algebraMap K L)) :
    v₁.IsEquiv v₂ :=
  (Valuation.isEquiv_iff_valuationSubring _ _).mpr <| unique_valuationSubring_of_ext h₁ h₂

end value_ext

end DiscreteValuation

namespace ValAlgEquiv

open DiscreteValuation

variable [CompleteSpace K] [IsDiscrete vK.v] [vL : Valued L ℤₘ₀]
variable [ValAlgebra K L] [FiniteDimensional K L]

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
def equivAlgEquiv : (L ≃ₐ[K] L) ≃* (L ≃ₐv[K] L) := {
  fromAlgEquiv K L with
  invFun := toAlgEquiv
  left_inv := sorry
  right_inv := sorry
}

end ValAlgEquiv
