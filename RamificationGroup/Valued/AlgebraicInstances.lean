import RamificationGroup.Valued.Hom.ValExtension'
import RamificationGroup.Valuation.Extension
import RamificationGroup.Valued.Hom.Discrete
import RamificationGroup.ForMathlib.Algebra.Algebra.Basic


open DiscreteValuation Valuation Valued ExtDVR IsValExtension Polynomial

-- `IsDiscrete vK.v` may be weakened to `Nontrivial vK.v`.
variable (K L : Type*) [Field K] [Field L] [vK : Valued K ℤₘ₀] [IsDiscrete vK.v] [vL : Valued L ℤₘ₀] [Algebra K L] [IsValExtension K L] [FiniteDimensional K L]

section algebra_instances

/-- 1. The conditions might be too strong.
2. The proof is almost the SAME with `Valuation.mem_integer_of_mem_integral_closure`. -/
instance : IsIntegrallyClosed 𝒪[K] := by
  rw [isIntegrallyClosed_iff K]
  intro x ⟨p, hp⟩
  by_cases xne0 : x = 0
  · subst xne0; use 0; simp only [_root_.map_zero]
  by_cases vxgt1 : v x ≤ 1
  · use ⟨x, vxgt1⟩; rfl
  · exfalso
    push_neg at vxgt1
    letI : Invertible x := invertibleOfNonzero xne0
    have : v (aeval x⁻¹ (p.reverse - 1)) < 1 := by
      apply aeval_valuationSubring_lt_one_of_lt_one_self
      · simp only [coeff_sub, coeff_zero_reverse, hp.1, Monic.leadingCoeff, coeff_one_zero, sub_self]
      · apply (one_lt_val_iff v xne0).mp vxgt1
    apply ne_of_lt this
    have : aeval x⁻¹ (p.reverse - 1) = -1 := by
      rw [← add_neg_eq_zero]
      ring_nf
      simp only [_root_.map_add, _root_.map_neg, _root_.map_one, add_neg_cancel_left]
      rw [← invOf_eq_inv x, aeval_def, Polynomial.eval₂_reverse_eq_zero_iff, hp.2]
    rw [this, Valuation.map_neg, Valuation.map_one]

attribute [local instance 1001] Algebra.toSMul

instance : IsScalarTower 𝒪[K] 𝒪[L] L := inferInstanceAs (IsScalarTower vK.v.integer vL.v.integer L)

instance [CompleteSpace K] : Algebra.IsIntegral 𝒪[K] 𝒪[L] where
  isIntegral := by
    intro ⟨x, hx⟩
    rw [show x ∈ 𝒪[L] ↔ x ∈ vL.v.valuationSubring by rfl,
      (Valuation.isEquiv_iff_valuationSubring _ _).mp
        (extension_valuation_equiv_extendedValuation_of_discrete (IsValExtension.val_isEquiv_comap (R := K) (A := L))),
      ← ValuationSubring.mem_toSubring, ← Extension.integralClosure_eq_integer, Subalgebra.mem_toSubring] at hx
    rcases hx with ⟨p, hp⟩
    refine ⟨p, hp.1, ?_⟩
    ext
    rw [show (0 : 𝒪[L]).val = 0 by rfl, ← hp.2]
    calc
      _ = 𝒪[L].subtype (eval₂ (algebraMap 𝒪[K] 𝒪[L]) ⟨x, hx⟩ p) := rfl
      _ = _ := by
        rw [Polynomial.hom_eval₂]
        simp only [Subring.coeSubtype]
        congr

instance [CompleteSpace K] : IsIntegralClosure 𝒪[L] 𝒪[K] L := sorry
  -- IsIntegralClosure.of_isIntegrallyClosed 𝒪[L] 𝒪[K] L

instance : DiscreteValuationRing 𝒪[K] :=
  inferInstanceAs (DiscreteValuationRing vK.v.valuationSubring)

theorem aux6 [CompleteSpace K] : DiscreteValuationRing 𝒪[L] :=
  valuationSubring_DVR_of_equiv_discrete
    (extension_valuation_equiv_extendedValuation_of_discrete
      (IsValExtension.val_isEquiv_comap (R := K) (A := L)))

/-- Can't be inferred automatically. -/
instance [CompleteSpace K] [Algebra.IsSeparable K L] : IsNoetherian 𝒪[K] 𝒪[L] :=
  IsIntegralClosure.isNoetherian 𝒪[K] K L 𝒪[L]

-- noncomputable def PowerBasisValExtension [CompleteSpace K] [Algebra.IsSeparable K L] [Algebra.IsSeparable (LocalRing.ResidueField 𝒪[K]) (LocalRing.ResidueField 𝒪[L])] : PowerBasis 𝒪[K] 𝒪[L] :=
--   letI : Nontrivial vL.v := nontrivial_of_valExtension K L
--   letI : DiscreteValuationRing 𝒪[L] := aux6 K L
--   PowerBasisExtDVR (integerAlgebra_injective K L)

example [CompleteSpace K] [Algebra.IsSeparable K L] :
  Algebra.FiniteType 𝒪[K] 𝒪[L] := inferInstance

end algebra_instances

section ramification

section general

variable (K L : Type*) {ΓK ΓL : outParam Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]
    [Algebra K L] [vK : Valued K ΓK] [vL : Valued L ΓL] [IsValExtension K L]

/-- Should be renamed -/
noncomputable def LocalField.ramificationIdx : ℕ :=
  LocalRing.ramificationIdx 𝒪[K] 𝒪[L]

end general

section discrete

variable (K L : Type*) {ΓK ΓL : outParam Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    [vK : Valued K ℤₘ₀] [IsDiscrete vK.v]
    [vL : Valued L ℤₘ₀] [IsValExtension K L]

open LocalField ExtDVR

-- theorem integerAlgebra_integral_of_integral

#check exists_Uniformizer_ofDiscrete
theorem ramificationIdx_ne_zero [CompleteSpace K] : ramificationIdx K L ≠ 0 := by
  sorry
  -- letI : DiscreteValuationRing 𝒪[L] := aux6 K L
  -- apply ramificationIdx_ne_zero_of_injective_of_integral (integerAlgebra_injective K L)
  -- rw [← Algebra.isIntegral_iff_isIntegral]
  -- infer_instance

theorem aux0 [CompleteSpace K] [IsDiscrete vL.v] : vL.v = extendedValuation K L := by
  rw [← isEquiv_iff_eq]
  apply extension_valuation_equiv_extendedValuation_of_discrete val_isEquiv_comap

variable {L} in
theorem aux3 [IsDiscrete vK.v] [IsDiscrete vL.v]
  (x : K) : vL.v (algebraMap K L x) = (vK.v x) ^ (ramificationIdx K L) := by
  sorry


end discrete

#check Ideal.ramificationIdx

end ramification
