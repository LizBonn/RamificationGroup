import RamificationGroup.UpperNumbering
import RamificationGroup.Upper_phiComp

open AlgEquiv DiscreteValuation Valuation Valued HerbrandFunction

variable {K K' L : Type*} {ΓK : outParam Type*} [Field K] [Field K'] [Field L] [vK' : Valued K' ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK'.v] [IsDiscrete vL.v] [Algebra K L] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L] [IsValExtension K' L] [Normal K K'] [Normal K L] [FiniteDimensional K L] [FiniteDimensional K K'] [FiniteDimensional K' L] [Algebra.IsSeparable K' L] [Algebra (LocalRing.ResidueField (Valued.integer K')) (LocalRing.ResidueField (Valued.integer L))] [Algebra.IsSeparable (LocalRing.ResidueField (Valued.integer K')) (LocalRing.ResidueField (Valued.integer L))] [CompleteSpace K']

variable [vK : Valued K ℤₘ₀] [IsDiscrete vK.v] [CompleteSpace K] [IsValExtension K K'] [IsValExtension K L]

variable (σ : K' ≃ₐ[K] K')

theorem truncatedJ_refl {u : ℚ} : truncatedJ (K := K) (K' := K') L u .refl = u := by
  simp only [truncatedJ]
  sorry

--check if this is right
theorem FuncJ_untop_of_nerefl (h : σ ≠ .refl) : FuncJ L σ ≠ ⊤ := by sorry


-- theorem aux9 (h : σ ≠ .refl) : i_[K'/K] σ ≠ ⊤ := by sorry

-- theorem lemma3_untop' (h : σ ≠ .refl) : phi K' L ((FuncJ L σ).untop (FuncJ_untop_iff_nerefl σ h)) = (1 / Nat.card G(L/K)_[0]) * ((Finset.sum (⊤ : Finset (L ≃ₐ[K] L)) (AlgEquiv.truncatedLowerIndex K L (((FuncJ L σ).untop (FuncJ_untop_iff_nerefl σ h)) + 1) ·))) - 1 := by sorry
open Classical

#synth Group (L ≃ₐ[K'] L)
#synth Fintype (L ≃ₐ[K] L)


#check ((⊤ \ {.refl}) : Finset (L ≃ₐ[K] L))

theorem truncatedJ_eq_truncated_FuncJ (u : ℚ) : truncatedJ L u σ =
  if h : FuncJ L σ = ⊤ then u
  else min ((FuncJ L σ).untop h) u := by
    sorry

#check prop3

theorem preimage_restrictNormalHom_untop (hsig : σ ≠ .refl) : ∀ s ∈ ((restrictNormalHom K')⁻¹' {σ}), i_[L/K] s ≠ ⊤ := by sorry

-- theorem sum_lt_top_of_sigma_ne_refl (hsig : σ ≠ .refl) : (∑ s ∈ ((restrictNormalHom K')⁻¹' {σ}), i_[L/K] s) ≠ ⊤ := by
--   apply ne_of_lt
--   apply WithTop.sum_lt_top.2
--   intro i hi
--   sorry

theorem preimage_untop (hsig : σ ≠ .refl) {x : L ≃ₐ[K'] L} {s : L ≃ₐ[K] L} (h1 : s ∈ ((restrictNormalHom K')⁻¹' {σ})) : i_[L/K] ((restrictScalarsHom K x) * s) ≠ ⊤ := by sorry

#check Finset.sum_of_injOn
theorem sum_preimage_eq_sum_subgroup (hsig : σ ≠ .refl) {s : L ≃ₐ[K] L} (h1 : s ∈ ((restrictNormalHom K')⁻¹' {σ})) (h2 : i_[L/K] s = FuncJ L σ) : ∑ x : ((restrictNormalHom K')⁻¹' {σ}), ((i_[L/K] x).untop (preimage_restrictNormalHom_untop (L := L) σ hsig x.1 x.2)) = ∑ x : (L ≃ₐ[K'] L), ((i_[L/K] ((restrictScalarsHom K x) * s)).untop (preimage_untop σ hsig h1)) := by
  let e : (L ≃ₐ[K'] L) → ((restrictNormalHom K' (K₁ := L))⁻¹' {σ}):= fun t => ⟨(AlgEquiv.restrictScalarsHom K t) * s, by
    simp only [Set.mem_preimage, _root_.map_mul, _root_.map_inv, Set.mem_singleton_iff, AlgEquiv.restrictNormalHom_restrictScalarsHom, one_mul]
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1
    exact h1⟩
  symm
  apply Finset.sum_of_injOn e
  · sorry
  · simp only [Finset.coe_univ, Set.mapsTo_univ_iff, Set.mem_univ, implies_true, e]
  · intro i hi1 hi2
    sorry
  · intro i hi
    simp only

theorem Finset.sum_untop {α : Type*} {s : Finset α} {f : α → ℕ∞} (h : ∑ x ∈ s, f x ≠ ⊤) : ∑ x : s, ((f x).untop (ne_of_lt ((WithTop.sum_lt_top).1 (Ne.lt_top' h.symm) x.1 x.2))) = (∑ x ∈ s, f x).untop h := by
  sorry

#check WithTop.untop_eq_iff
theorem prop3_aux (hsig : σ ≠ .refl) {s : L ≃ₐ[K] L} (h1 : s ∈ ((restrictNormalHom K')⁻¹' {σ})) (h2 : i_[L/K] s = FuncJ L σ) : (LocalField.ramificationIdx K' L) * (lowerIndex K K' σ).untop (lowerIndex_ne_one (mem_decompositionGroup σ) hsig) = (∑ x : (L ≃ₐ[K'] L), (i_[L/K] ((restrictScalarsHom K x) * s)).untop (preimage_untop σ hsig h1)) := by

  sorry

theorem preimage_lowerIndex_eq_FuncJ (hsig : σ ≠ .refl) : ∃ x : (L ≃ₐ[K] L), x ∈ ((restrictNormalHom K')⁻¹' {σ}) ∧ i_[L/K] x = FuncJ L σ := by sorry

theorem lowerIndex_eq_phi_FuncJ_of_ne_refl (hsig : σ ≠ .refl) : (lowerIndex K K' σ).untop (lowerIndex_ne_one (mem_decompositionGroup σ) hsig) = phi K' L ((FuncJ L σ).untop (FuncJ_untop_of_nerefl σ hsig)) + 1 := by
  obtain ⟨s, hs1, hs2⟩ := preimage_lowerIndex_eq_FuncJ (K' := K') (L := L) σ hsig
  suffices h : (LocalField.ramificationIdx K' L) * (lowerIndex K K' σ).untop (lowerIndex_ne_one (mem_decompositionGroup σ) hsig) = (LocalField.ramificationIdx K' L) * (phi K' L ((FuncJ L σ).untop (FuncJ_untop_of_nerefl σ hsig)) + 1) from by
    simp only [mul_eq_mul_left_iff, Nat.cast_eq_zero] at h
    rcases h with h | h
    · exact h
    · absurd h
      apply ramificationIdx_ne_zero
  rw [← Nat.cast_mul, prop3_aux (K := K) (K' := K') (L := L) σ hsig hs1 hs2, phi_eq_sum_inf, RamificationIdx_eq_card_of_inertia_group, sub_add_cancel, ← mul_assoc, mul_one_div_cancel, one_mul, Nat.cast_sum]
  apply Finset.sum_congr rfl
  · intro x hx
    sorry
  · simp only [ne_eq, Nat.cast_eq_zero]
    apply ramificationIdx_ne_zero
  -- let e : (L ≃ₐ[K'] L) → ↑(⇑(restrictNormalHom K' (K₁ := L)) ⁻¹' {σ}) := fun x => ⟨(AlgEquiv.restrictScalarsHom K x) * s⁻¹, by
  --   simp only [Set.mem_preimage, _root_.map_mul, _root_.map_inv, Set.mem_singleton_iff, AlgEquiv.restrictNormalHom_restrictScalarsHom, one_mul]
  --   simp only [Set.mem_preimage, Set.mem_singleton_iff] at hs1
  --   sorry⟩
  -- suffices h : (LocalField.ramificationIdx K L) * (lowerIndex K K' σ).untop (lowerIndex_ne_one (mem_decompositionGroup σ) hsig) = (LocalField.ramificationIdx K L) * (phi K' L ((FuncJ L σ).untop (FuncJ_untop_of_nerefl σ hsig)) + 1) from by
  -- rw [prop3_aux (L := L) σ hsig, phi_eq_sum_inf, RamificationIdx_eq_card_of_inertia_group, sub_add_cancel, Nat.cast_div, div_eq_mul_one_div, mul_comm]
  -- simp only [one_div, Finset.top_eq_univ, mul_eq_mul_left_iff, inv_eq_zero, Nat.cast_eq_zero]
  -- left
  -- repeat sorry

theorem truncatedJ_eq_trunc_iff_lowerIdx_le_phi {u : ℚ} (hsig : σ ≠ .refl) :  min (phi K' L u + 1) ((i_[K'/K] σ).untop (lowerIndex_ne_one (mem_decompositionGroup σ) hsig)) = phi K' L u + 1 ↔ truncatedJ L u σ = u := by
  constructor
  · intro hu
    simp only [truncatedJ_eq_truncated_FuncJ, (FuncJ_untop_of_nerefl σ hsig), ↓reduceDIte]
    rw [min_eq_right]
    suffices h : phi K' L u ≤ phi K' L ((FuncJ L σ).untop (FuncJ_untop_of_nerefl σ hsig)) from by
      apply (StrictMono.le_iff_le (phi_strictMono K' L)).1 h
    rw [← add_le_add_iff_right (a := 1), ← lowerIndex_eq_phi_FuncJ_of_ne_refl σ hsig, ← hu]
    apply min_le_right
  · intro hu
    rw [min_eq_left]
    simp only [truncatedJ_eq_truncated_FuncJ, (FuncJ_untop_of_nerefl σ hsig), ↓reduceDIte] at hu
    rw [lowerIndex_eq_phi_FuncJ_of_ne_refl (L := L) σ hsig, add_le_add_iff_right]
    apply (phi_strictMono K' L).monotone
    rw [← hu]
    apply min_le_left

theorem lemma3_aux' (u : ℚ) : σ.truncatedLowerIndex K K' (phi K' L u + 1) = (1 / LocalField.ramificationIdx K' L) * (∑ s in (⊤ : Finset (L ≃ₐ[K'] L)), (AlgEquiv.truncatedLowerIndex K L (truncatedJ L u σ + 1) (AlgEquiv.restrictScalars K s))) := by
  by_cases hsig : σ = .refl
  · conv =>
      left
      simp only [hsig, truncatedLowerIndex, lowerIndex_refl, ↓reduceDIte, one_div, Finset.top_eq_univ, lowerIndex_restrictScalars]
    conv =>
      right
      simp only [hsig, truncatedJ_refl]
    rw [phi_eq_sum_inf K' L, RamificationIdx_eq_card_of_inertia_group]
    simp only [one_div, Finset.top_eq_univ, sub_add_cancel, truncatedLowerIndex_restrictScalars]
  · have h : ¬ lowerIndex K K' σ = ⊤ := by
      apply lowerIndex_ne_one ?_ hsig
      apply mem_decompositionGroup σ
    conv =>
      left
      simp only [truncatedLowerIndex, h, ↓reduceDIte]
    have hunion : (⊤ : Finset (L ≃ₐ[K'] L)) = ((⊤ \ {.refl}) : Finset (L ≃ₐ[K'] L)) ∪ ({.refl} : Finset (L ≃ₐ[K'] L)) := by
      simp only [Finset.top_eq_univ, Finset.sdiff_union_self_eq_union, Finset.left_eq_union, Finset.subset_univ]
    have hrefl : ∑ x ∈ ({.refl} : Finset (L ≃ₐ[K'] L)), i_[L/K]ₜ (truncatedJ L u σ + 1) (restrictScalars K x) = truncatedJ L u σ + 1 := by
      simp only [truncatedLowerIndex_restrictScalars, Finset.sum_singleton, truncatedLowerIndex_refl]
    rw [hunion, Finset.sum_union, hrefl]
    by_cases hu : min (phi K' L u + 1) ↑(WithTop.untop ( i_[K'/K] σ) h) = phi K' L u + 1
    · have hu' : truncatedJ L u σ = u := by
        apply (truncatedJ_eq_trunc_iff_lowerIdx_le_phi (K := K) (K' := K') (L := L) σ hsig).1 hu
      rw [hu, hu', phi_eq_sum_inf, RamificationIdx_eq_card_of_inertia_group]
      simp only [one_div, Finset.top_eq_univ, sub_add_cancel, truncatedLowerIndex_restrictScalars, Finset.subset_univ, Finset.sum_sdiff_eq_sub, Finset.sum_singleton, truncatedLowerIndex_refl]
    · have hu' : truncatedJ L u σ = ↑(WithTop.untop (FuncJ L σ) (FuncJ_untop_of_nerefl σ hsig)) := by
        suffices h : ¬ truncatedJ L u σ = u from by
          simp only [truncatedJ_eq_truncated_FuncJ, FuncJ_untop_of_nerefl σ hsig, ↓reduceDIte] at h ⊢
          apply Classical.or_iff_not_imp_right.1 (min_choice (((FuncJ L σ).untop (FuncJ_untop_of_nerefl σ hsig)) : ℚ) u) h
        by_contra hc
        absurd hu
        apply (truncatedJ_eq_trunc_iff_lowerIdx_le_phi (K := K) (K' := K') (L := L) σ hsig).2 hc
      simp only [Classical.or_iff_not_imp_left.1 (min_choice (phi K' L u + 1) (↑(WithTop.untop ( i_[K'/K] σ) h))) hu, hu']
      rw [lowerIndex_eq_phi_FuncJ_of_ne_refl (L := L) σ hsig, phi_eq_sum_inf, RamificationIdx_eq_card_of_inertia_group, sub_add_cancel]
      simp only [one_div, Finset.top_eq_univ, truncatedLowerIndex_restrictScalars, Finset.subset_univ, Finset.sum_sdiff_eq_sub, Finset.sum_singleton, truncatedLowerIndex_refl, sub_add_cancel]
    exact Finset.sdiff_disjoint
