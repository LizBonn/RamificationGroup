import RamificationGroup.UpperNumbering
import RamificationGroup.Upper_phiComp

open AlgEquiv DiscreteValuation Valuation Valued HerbrandFunction

variable {K K' L : Type*} {ΓK : outParam Type*} [Field K] [Field K'] [Field L] [vK' : Valued K' ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK'.v] [IsDiscrete vL.v] [Algebra K L] [Algebra.IsSeparable K L] [Algebra K K'] [Algebra.IsSeparable K K'] [Algebra K' L] [IsScalarTower K K' L] [IsValExtension vK'.v vL.v] [Normal K K'] [Normal K L] [FiniteDimensional K L] [FiniteDimensional K K'] [FiniteDimensional K' L] [Algebra.IsSeparable K' L] [Algebra (IsLocalRing.ResidueField (Valued.integer K')) (IsLocalRing.ResidueField (Valued.integer L))] [Algebra.IsSeparable (IsLocalRing.ResidueField (Valued.integer K')) (IsLocalRing.ResidueField (Valued.integer L))] [CompleteSpace K']

variable [vK : Valued K ℤₘ₀] [IsDiscrete vK.v] [CompleteSpace K] [IsValExtension vK.v vK'.v] [IsValExtension vK.v vL.v]

variable (σ : K' ≃ₐ[K] K')



#check restrictNormalHom
#check truncatedLowerIndex_refl
theorem truncatedJ_refl {u : ℚ} : truncatedJ (K := K) (K' := K') L u .refl = u - 1:= by
  simp only [truncatedJ]
  apply le_antisymm
  · apply Finset.max'_le
    simp only [Finset.mem_image, Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, tsub_le_iff_right]
    intro y _
    unfold truncatedLowerIndex
    by_cases h' : i_[L/K] y = ⊤
    · simp only [h', ↓reduceDIte, sub_add_cancel, le_refl]
    · simp only [h', ↓reduceDIte, sub_add_cancel, min_le_iff, le_refl, true_or]
  · apply Finset.le_max'
    simp only [Finset.mem_image, Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]
    use AlgEquiv.refl
    constructor
    · apply (restrictNormalHom K').map_one
    · rw [truncatedLowerIndex_refl]


theorem FuncJ_refl (h : σ = .refl) : FuncJ L σ = ⊤ := by
  unfold FuncJ
  apply le_antisymm
  · apply le_top
  · apply Finset.le_max'
    simp only [Finset.mem_image, Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]
    use .refl
    constructor
    · rw [h]
      apply (restrictNormalHom K').map_one
    · rw [lowerIndex_refl]



--check if this is right
#check lowerIndex_ne_refl
theorem FuncJ_untop_of_nerefl (h : σ ≠ .refl) : FuncJ L σ ≠ ⊤ := by
  unfold FuncJ
  apply lt_top_iff_ne_top.1
  apply (Finset.max'_lt_iff _ _).2
  simp only [Finset.mem_image, Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro a ha
  by_contra hc
  push_neg at hc
  rw [WithTop.top_le_iff] at hc
  have h1 : a = .refl := by
    by_contra hc'
    have h1' : i_[L/K] a ≠ ⊤ := lowerIndex_ne_refl (K := K) (L := L) hc'
    apply h1' hc
  have h2 : σ = .refl := by
    rw [← ha, h1]
    apply (restrictNormalHom K').map_one
  apply h h2

theorem FuncJ_untop_iff_nerefl : σ ≠ .refl ↔ FuncJ L σ ≠ ⊤ := by
  constructor
  · exact fun a ↦ FuncJ_untop_of_nerefl σ a
  · intro h
    by_contra hc
    absurd h
    exact FuncJ_refl σ hc

-- theorem aux9 (h : σ ≠ .refl) : i_[K'/K] σ ≠ ⊤ := by sorry

-- theorem lemma3_untop' (h : σ ≠ .refl) : phi K' L ((FuncJ L σ).untop (FuncJ_untop_iff_nerefl σ h)) = (1 / Nat.card G(L/K)_[0]) * ((Finset.sum (⊤ : Finset (L ≃ₐ[K] L)) (AlgEquiv.truncatedLowerIndex K L (((FuncJ L σ).untop (FuncJ_untop_iff_nerefl σ h)) + 1) ·))) - 1 := by sorry
open Classical


theorem preimage_lowerIndex_eq_FuncJ (hsig : σ ≠ .refl) : ∃ x : (L ≃ₐ[K] L), x ∈ ((restrictNormalHom K')⁻¹' {σ}) ∧ i_[L/K] x = FuncJ L σ := by
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  by_contra hc
  push_neg at hc
  have h : FuncJ L σ < FuncJ L σ := by
    conv =>
      left
      unfold FuncJ
    apply (Finset.max'_lt_iff _ _).2
    intro y hy
    simp only [Finset.mem_image, Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hy
    obtain ⟨a, ha, ha2⟩ := hy
    rw [← ha2]
    apply lt_of_le_of_ne
    unfold FuncJ
    apply Finset.le_max'
    simp only [Finset.mem_image, Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]
    use a
    by_contra hc'
    absurd hc
    push_neg
    use a
  exact (lt_self_iff_false (FuncJ L σ)).mp h


#check ((⊤ \ {.refl}) : Finset (L ≃ₐ[K] L))

theorem WithTop.untop_add_one (x : WithTop ℕ) (h : x ≠ ⊤) : WithTop.untop x h + 1 = WithTop.untop (x + 1) (WithTop.add_ne_top.2 ⟨h, WithTop.one_ne_top⟩) := by
  symm
  apply (WithTop.untop_eq_iff _).2
  simp only [coe_add, coe_untop, coe_one]

theorem preimage_lowerIndex_le_FuncJ {a : L ≃ₐ[K] L} (ha : restrictNormalHom K' a = σ) : i_[L/K] a ≤ FuncJ L σ := by
  unfold FuncJ
  apply Finset.le_max'
  simp only [Finset.mem_image, Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]
  use a

theorem truncatedJ_eq_truncated_FuncJ (u : ℚ) : truncatedJ L u σ =
  if h : FuncJ L σ = ⊤ then u - 1
  else (min (((FuncJ L σ).untop h) : ℚ) u) - 1:= by
    unfold truncatedJ
    by_cases h' : FuncJ L σ = ⊤
    · have hsig : σ = .refl := by
        by_contra hc
        have hc' : FuncJ L σ ≠ ⊤ := by exact FuncJ_untop_of_nerefl (K := K) (K' := K') (L := L) σ hc
        apply hc' h'
      simp only [h', ↓reduceDIte]
      apply le_antisymm
      · apply Finset.max'_le
        simp only [Finset.mem_image, Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, tsub_le_iff_right, sub_add_cancel]
        intro y hy
        unfold truncatedLowerIndex
        by_cases h' : i_[L/K] y = ⊤
        · simp only [h', ↓reduceDIte, sub_add_cancel, le_refl]
        · simp only [h', ↓reduceDIte, sub_add_cancel, min_le_iff, le_refl, true_or]
      · apply Finset.le_max'
        simp only [Finset.mem_image, Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, sub_left_inj]
        use AlgEquiv.refl
        constructor
        · rw [hsig]
          apply (restrictNormalHom K').map_one
        · rw [truncatedLowerIndex_refl]
    · simp only [h', ↓reduceDIte]
      symm
      rw [sub_eq_iff_eq_add]
      apply min_eq_iff.2
      by_cases hc : ((FuncJ L σ).untop h') ≤ u
      · left
        constructor
        · rw [← sub_eq_iff_eq_add]
          unfold FuncJ truncatedLowerIndex
          apply le_antisymm
          · apply Finset.le_max'
            simp only [decompositionGroup_eq_top, Subgroup.mem_top, lowerIndex_eq_top_iff_eq_refl, Finset.mem_image, Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, sub_left_inj]
            have hsig : σ ≠ .refl := by
              exact (FuncJ_untop_iff_nerefl σ).mpr h'
            obtain ⟨a, ha1, ha2⟩ := preimage_lowerIndex_eq_FuncJ (K := K) (K' := K') (L := L) σ hsig
            use a
            constructor
            · simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha1
              exact ha1
            · have ha3 : a ≠ .refl := by
                by_contra hc
                absurd h'
                rw [← ha2]
                refine (lowerIndex_eq_top_iff_eq_refl ?_).mpr hc
                exact mem_decompositionGroup a
              simp only [ha3, ↓reduceDIte, ha2, min_eq_right hc]
              simp only [FuncJ]
          · apply Finset.max'_le
            simp only [decompositionGroup_eq_top, Subgroup.mem_top, lowerIndex_eq_top_iff_eq_refl, Finset.mem_image, Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, tsub_le_iff_right,sub_add_cancel]
            intro a ha
            have ha3 : a ≠ .refl := by
              by_contra hc'
              rw [hc'] at ha
              have hsig : σ = .refl := by
                rw [← ha]
                apply (restrictNormalHom K').map_one
              absurd h'
              exact FuncJ_refl σ hsig
            simp only [ha3, ↓reduceDIte]
            rw [min_eq_right]
            simp only [Nat.cast_le]
            apply (WithTop.le_untop_iff _).2
            apply Finset.le_max'
            simp only [WithTop.coe_untop, Finset.mem_image, Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]
            use a
            apply le_trans _ hc
            simp only [Nat.cast_le]
            apply (WithTop.le_untop_iff _).2
            simp only [WithTop.coe_untop]
            apply preimage_lowerIndex_le_FuncJ σ ha
        · exact hc
      · right
        constructor
        · rw [← sub_eq_iff_eq_add]
          apply le_antisymm
          · push_neg at hc
            apply Finset.le_max'
            simp only [Finset.mem_image, Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, sub_left_inj]
            have hsig : σ ≠ .refl := (FuncJ_untop_iff_nerefl σ).mpr h'
            obtain ⟨a, ha1, ha2⟩ := preimage_lowerIndex_eq_FuncJ (K := K) (K' := K') (L := L) σ hsig
            use a
            refine ⟨ha1, ?_⟩
            unfold truncatedLowerIndex
            by_cases ha : i_[L/K] a = ⊤
            · simp only [ha, ↓reduceDIte]
            · simp only [ha, ↓reduceDIte, min_eq_left_iff]
              simp only [ha2]
              apply le_of_lt hc
          · apply Finset.max'_le
            simp only [Finset.mem_image, Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, tsub_le_iff_right,sub_add_cancel]
            intro a ha
            unfold truncatedLowerIndex
            by_cases ha : i_[L/K] a = ⊤
            · simp only [ha, ↓reduceDIte, le_refl]
            · simp only [ha, ↓reduceDIte, min_le_iff, le_refl, true_or]
        · apply le_of_lt
          push_neg at hc
          exact hc
        -- · symm
        --   apply le_antisymm
        --   · apply Finset.max'_le
        --     simp only [Finset.mem_image, Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, tsub_le_iff_right, sub_add_cancel]
        --     intro a ha
        --     unfold truncatedLowerIndex
        --     by_cases hc' : i_[L/K] a = ⊤
        --     · simp only [hc', ↓reduceDIte, le_refl]
        --     · simp only [hc', ↓reduceDIte, min_le_iff, le_refl, true_or]
        --   · apply Finset.le_max'
        --     simp only [Finset.mem_image, Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, sub_left_inj]
        --     have hsig : σ ≠ .refl := by
        --       by_contra hcon
        --       have h'' : FuncJ L σ = ⊤ := FuncJ_refl (K := K) (K' := K') (L := L) σ hcon
        --       apply h' h''
        --     obtain ⟨a, ha1, ha2⟩ :=  preimage_lowerIndex_eq_FuncJ (K := K) (K' := K') (L := L) σ hsig
        --     use a
        --     constructor
        --     · simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha1
        --       exact ha1
        --     · push_neg at hc
        --       unfold truncatedLowerIndex
        --       by_cases hcase : i_[L/K] a = ⊤
        --       · simp only [hcase, ↓reduceDIte]
        --       · simp only [hcase, ↓reduceDIte, min_eq_left_iff]
        --         simp only [ha2]
        --         rw [← WithTop.untop_add_one _ h']
        --         apply le_of_lt
        --         simp only [Nat.cast_add, Nat.cast_one]
        --         linarith [hc]
        -- · linarith [hc]

#check eq_false
#check of_eq_false
#check lowerIndex_ne_refl
theorem preimage_restrictNormalHom_untop (hsig : σ ≠ .refl) (s : L ≃ₐ[K] L) (hs : s ∈ ((restrictNormalHom K')⁻¹' {σ})) : i_[L/K] s ≠ ⊤ := by
  by_contra hc
  have hs' : s = .refl := by
    by_contra hc'
    have hs' : i_[L/K] s ≠ ⊤ := by exact lowerIndex_ne_refl (K := K) (L := L) hc'
    apply hs' hc
  have hsig' : σ = .refl := by
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hs'] at hs
    rw [← hs]
    apply (restrictNormalHom K').map_one
  apply hsig hsig'


-- theorem sum_lt_top_of_sigma_ne_refl (hsig : σ ≠ .refl) : (∑ s ∈ ((restrictNormalHom K')⁻¹' {σ}), i_[L/K] s) ≠ ⊤ := by
--   apply ne_of_lt
--   apply WithTop.sum_lt_top.2
--   intro i hi
--   sorry

theorem preimage_untop (hsig : σ ≠ .refl) {x : L ≃ₐ[K'] L} {s : L ≃ₐ[K] L} (h1 : s ∈ ((restrictNormalHom K')⁻¹' {σ})) : i_[L/K] ((restrictScalarsHom K x) * s) ≠ ⊤ := by
  apply lowerIndex_ne_one
  exact mem_decompositionGroup ((restrictScalarsHom K) x * s)
  by_contra hc
  have hsig' : σ = .refl := by
    symm
    calc
    _ = restrictNormalHom K' (K₁ := L) .refl := by
      symm
      exact (restrictNormalHom (F := K) K' (K₁ := L)).map_one
    _ = restrictNormalHom K' ((restrictScalarsHom K) x * s) := by rw [hc]
    _ = (restrictNormalHom K' ((restrictScalarsHom K) x)) * ((restrictNormalHom K') s) := MonoidHom.map_mul (restrictNormalHom K') ((restrictScalarsHom K) x) s
    _ = σ := by
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1
      rw [restrictNormalHom_restrictScalarsHom, h1, one_mul]
  apply hsig hsig'

#check AlgEquiv
theorem preimage_mul_preimage_inv_mem_subgroup (i s : L ≃ₐ[K] L) (hi : i ∈ ((restrictNormalHom K')⁻¹' {σ})) (hs : s ∈ ((restrictNormalHom K')⁻¹' {σ})) : ∃ x : L ≃ₐ[K'] L, restrictScalarsHom K x = i * s⁻¹ := by
  let x : L ≃ₐ[K'] L :=
  {
    (i * s⁻¹) with
    commutes' := by
      dsimp
      intro r
      apply (EquivLike.apply_eq_iff_eq i⁻¹).1
      have hi' : i⁻¹ = i.invFun := by exact rfl
      rw [hi', ← Function.comp_apply (f := i.invFun) (g := i)]
      simp only [toEquiv_eq_coe, Equiv.invFun_as_coe, symm_toEquiv_eq_symm, EquivLike.coe_coe, Function.comp_apply, symm_apply_apply]
--         simp only [AlgEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AlgEquiv.symm_toEquiv_eq_symm, EquivLike.coe_coe, Function.comp_apply, AlgEquiv.apply_symm_apply]
--         rw [Set.mem_preimage, Set.mem_singleton_iff] at hb
      simp at hi hs
      have hs' : restrictNormalHom K' s⁻¹ = restrictNormalHom K' i.symm := by
        rw [MonoidHom.map_inv (restrictNormalHom K') s, hs, ← hi, ← MonoidHom.map_inv (restrictNormalHom K') i]
        exact rfl
      rw [← AlgEquiv.restrictNormal_commutes, ← AlgEquiv.restrictNormal_commutes, restrictNormal_restrictNormalHom s⁻¹, restrictNormal_restrictNormalHom, hs']
  }
  use x
  simp only [toEquiv_eq_coe, x]
  exact rfl

#check Finset.sum_of_injOn
theorem sum_preimage_eq_sum_subgroup (hsig : σ ≠ .refl) {s : L ≃ₐ[K] L} (h1 : s ∈ ((restrictNormalHom K')⁻¹' {σ})) : ∑ x : ((restrictNormalHom K')⁻¹' {σ}), ((i_[L/K] x).untop (preimage_restrictNormalHom_untop (L := L) σ hsig x.1 x.2)) = ∑ x : (L ≃ₐ[K'] L), ((i_[L/K] ((restrictScalarsHom K x) * s)).untop (preimage_untop σ hsig h1)) := by
  let e : (L ≃ₐ[K'] L) → ((restrictNormalHom K' (K₁ := L))⁻¹' {σ}) := fun t => ⟨(AlgEquiv.restrictScalarsHom K t) * s, by
    simp only [Set.mem_preimage, _root_.map_mul, _root_.map_inv, Set.mem_singleton_iff, AlgEquiv.restrictNormalHom_restrictScalarsHom, one_mul]
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1
    exact h1⟩
  symm
  apply Finset.sum_of_injOn e
  · intro a ha b hb hab
    unfold e at hab
    simp only [Subtype.mk.injEq, mul_left_inj] at hab
    apply AlgEquiv.restrictScalarsHom_injective K hab
  · simp only [Finset.coe_univ, Set.mapsTo_univ_iff, Set.mem_univ, implies_true, e]
  · intro i hi1 hi2
    simp only [Finset.coe_univ, Set.image_univ, Set.mem_range, not_exists, e] at hi2
    absurd hi2
    push_neg
    obtain ⟨x, hx⟩ := preimage_mul_preimage_inv_mem_subgroup (K := K) (K' := K') (L := L) σ i s (Subtype.coe_prop i) h1
    use x
    simp only [hx, inv_mul_cancel_right, Subtype.coe_eta]
  · intro i hi
    rfl


#check restrictScalarsHom

theorem Finset.sum_untop {α : Type*} {s : Finset α} {β : Type*} [AddCommMonoid β] [LT β] {f : α → WithTop β} (h : ∑ x : s, f x ≠ ⊤) : ∑ x : s, ((f x).untop (WithTop.lt_top_iff_ne_top.1 ((WithTop.sum_lt_top).1 (WithTop.lt_top_iff_ne_top.2
h) x (mem_univ x)))) = (∑ x : s, f x).untop h := by
  symm
  apply (WithTop.untop_eq_iff h).2
  simp only [univ_eq_attach, WithTop.coe_sum, WithTop.coe_untop]


--for lower
theorem prop3' (σ : K' ≃ₐ[K] K') (x : PowerBasis 𝒪[K] 𝒪[L]) (y : PowerBasis 𝒪[K'] 𝒪[L]) : ∑ s ∈ ((restrictNormalHom K')⁻¹' {σ}), i_[L/K] s = (LocalField.ramificationIdx K' L) * i_[K'/K] σ := by
  sorry

set_option maxHeartbeats 0
#check WithTop.untop_eq_iff
theorem prop3_aux (hsig : σ ≠ .refl) {s : L ≃ₐ[K] L} (h1 : s ∈ ((restrictNormalHom K')⁻¹' {σ})) (x : PowerBasis 𝒪[K] 𝒪[L]) (y : PowerBasis 𝒪[K'] 𝒪[L]) : (LocalField.ramificationIdx K' L) * (lowerIndex K K' σ).untop (lowerIndex_ne_one (mem_decompositionGroup σ) hsig) = (∑ x : (L ≃ₐ[K'] L), (i_[L/K] ((restrictScalarsHom K x) * s)).untop (preimage_untop σ hsig h1)) := by
  calc
    _ = ((LocalField.ramificationIdx K' L) * (lowerIndex K K' σ)).untop ?_ := by
      rw [← WithTop.coe_eq_coe, WithTop.coe_mul, WithTop.coe_untop, WithTop.coe_untop]
      rfl
      apply ne_of_lt (WithTop.mul_lt_top _ _)
    _ = (∑ x : ((restrictNormalHom K' (K₁ := L))⁻¹' {σ}), i_[L/K] x).untop ?_:= by
      rw [← WithTop.coe_eq_coe, WithTop.coe_untop, WithTop.coe_untop, ← prop3' (K := K) (K' := K') (L := L) σ x y]
      exact Eq.symm (Finset.sum_set_coe (⇑(restrictNormalHom K') ⁻¹' {σ}))
      exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
      apply WithTop.lt_top_iff_ne_top.2 (lowerIndex_ne_one (mem_decompositionGroup σ) hsig)
      apply WithTop.lt_top_iff_ne_top.1
      apply WithTop.sum_lt_top.2
      intro i hi
      apply WithTop.lt_top_iff_ne_top.2
      apply preimage_restrictNormalHom_untop (L := L) σ hsig i
      exact Subtype.coe_prop i
    _ = ∑ x : ((restrictNormalHom K')⁻¹' {σ}), ((i_[L/K] x).untop (preimage_restrictNormalHom_untop (L := L) σ hsig x.1 x.2)) := by
      apply (WithTop.untop_eq_iff ?_).2
      rw [WithTop.coe_sum]
      apply Finset.sum_congr rfl
      intro x hx
      symm
      apply WithTop.coe_untop
      apply WithTop.lt_top_iff_ne_top.1 (WithTop.sum_lt_top.2 ?_)
      intro i hi
      apply WithTop.lt_top_iff_ne_top.2
      apply preimage_restrictNormalHom_untop (K := K) (K' := K') (L := L) σ hsig
      exact Subtype.coe_prop i
    _ = _ := by
      exact sum_preimage_eq_sum_subgroup σ hsig h1

--for lower
theorem lowerIndex_inf_le_mul (s t : L ≃ₐ[K] L) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : min (i_[L/K] s) (i_[L/K] t) ≤ i_[L/K] (s * t) := by
  by_cases hc : i_[L/K] (s * t) = ⊤
  · rw [hc]
    exact le_top
  · have h1 : ∃ n : ℕ, i_[L/K] (s * t) = n := by
      use (WithTop.untop (i_[L/K] (s * t)) hc)
      symm
      apply WithTop.coe_untop
    obtain ⟨n, hn⟩ := h1
    have h2 : s * t ∉ G(L/K)_[n] := by
      by_contra hc'
      absurd hn
      have hn' : n + 1 ≤ i_[L/K] (s * t) := by
        apply (mem_lowerRamificationGroup_iff_of_generator hgen _ _).1 hc'
        exact mem_decompositionGroup (s * t)
      absurd hn
      apply ne_of_gt
      apply (ENat.add_one_le_iff (ENat.coe_ne_top n)).1 hn'
    by_contra hc'
    absurd h2
    push_neg at hc'
    rw [lt_min_iff, hn] at hc'
    have h3 : s ∈ G(L/K)_[n] := by
      apply (mem_lowerRamificationGroup_iff_of_generator hgen _ _).2
      exact Order.add_one_le_of_lt hc'.1
      exact mem_decompositionGroup s
    have h4 : t ∈ G(L/K)_[n] := by
      apply (mem_lowerRamificationGroup_iff_of_generator hgen _ _).2
      exact Order.add_one_le_of_lt hc'.2
      exact mem_decompositionGroup t
    exact (Subgroup.mul_mem_cancel_right G(L/K)_[↑n] h4).mpr h3

theorem WithTop.untop_lt_untop {a b : WithTop ℕ} (ha : a ≠ ⊤) (hb : b ≠ ⊤) : WithTop.untop a ha < WithTop.untop b hb ↔ a < b := by
  constructor<;>intro h
  · by_contra hc
    absurd h
    push_neg at hc ⊢
    apply (WithTop.le_untop_iff _).2
    simp only [WithTop.coe_untop]
    exact hc
  · apply (WithTop.lt_untop_iff _).2
    simp only [WithTop.coe_untop]
    exact h

--for lower
#check lowerIndex_restrictScalars
theorem lowerIndex_mul_le {s : L ≃ₐ[K] L} {x : L ≃ₐ[K'] L} (hsig : σ ≠ .refl) (hs : i_[L/K] s = FuncJ L σ) (htop : ¬ i_[L/K'] x = ⊤) (hlt : (WithTop.untop ( i_[L/K'] x) (of_eq_false (eq_false htop))) < (WithTop.untop (FuncJ L σ) (FuncJ_untop_of_nerefl σ hsig))) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : i_[L/K] ((restrictScalarsHom K) x * s) ≤ i_[L/K] ((restrictScalarsHom K) x) := by
  have h : i_[L/K'] x = i_[L/K] ((restrictScalarsHom K) x) := rfl
  have h1 : ∃ n : ℕ, i_[L/K] ((restrictScalarsHom K) x) = n := by
    use (WithTop.untop (i_[L/K] ((restrictScalarsHom K) x)) htop)
    symm
    apply WithTop.coe_untop
  obtain ⟨n, hn⟩ := h1
  have h2 : (restrictScalarsHom K) x ∉ G(L/K)_[n] := by
    by_contra hc
    have hn' : n + 1 ≤ i_[L/K] ((restrictScalarsHom K) x) := by
      apply (mem_lowerRamificationGroup_iff_of_generator hgen _ _).1 hc
      exact mem_decompositionGroup ((restrictScalarsHom K) x)
    absurd hn
    apply ne_of_gt
    apply (ENat.add_one_le_iff (ENat.coe_ne_top n)).1 hn'
  rw [hn]
  by_contra hc
  push_neg at hc
  have h3 : ((restrictScalarsHom K) x) * s ∈ G(L/K)_[n] := by
    apply (mem_lowerRamificationGroup_iff_of_generator hgen _ _).2
    exact Order.add_one_le_of_lt hc
    exact mem_decompositionGroup ((restrictScalarsHom K) x * s)
  have h4 : s ∈ G(L/K)_[n] := by
    apply (mem_lowerRamificationGroup_iff_of_generator hgen _ _).2
    apply Order.add_one_le_of_lt
    rw [← hn, hs, ← h]
    apply (WithTop.untop_lt_untop _ _).1 hlt
    exact mem_decompositionGroup s
  absurd h2
  exact (Subgroup.mul_mem_cancel_right G(L/K)_[n] h4).mp h3



--this is hard!!
--yeah
theorem lowerIndex_eq_inf (hsig : σ ≠ .refl) {s : L ≃ₐ[K] L} (h1 : s ∈ ((restrictNormalHom K')⁻¹' {σ})) (h2 : i_[L/K] s = FuncJ L σ) {x : L ≃ₐ[K'] L} {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : (i_[L/K] ((restrictScalarsHom K x) * s)).untop (preimage_untop (K := K) (K' := K') (L := L) σ hsig (s := s) (x := x) h1) = i_[L/K']ₜ ↑(WithTop.untop (FuncJ L σ) (FuncJ_untop_of_nerefl σ hsig)) x := by
  simp only [truncatedLowerIndex]
  by_cases htop : i_[L/K'] x = ⊤
  · simp only [htop, ↓reduceDIte]
    norm_cast
    apply le_antisymm
    · apply (WithTop.le_untop_iff _).2
      simp only [WithTop.coe_untop]
      apply preimage_lowerIndex_le_FuncJ σ
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1
      simp only [_root_.map_mul, h1, restrictNormalHom_restrictScalarsHom, one_mul]
    · apply (WithTop.untop_le_iff _).2
      rw [WithTop.coe_untop]
      apply le_trans _ (lowerIndex_inf_le_mul _ _ hgen)
      apply le_min_iff.2
      constructor
      · rw [lowerIndex_eq_top_iff_eq_refl] at htop
        have h : (restrictScalarsHom K (A := L) (S := K')) .refl = .refl (A₁ := L) := rfl
        rw [htop, h, lowerIndex_refl]
        apply le_top
        exact mem_decompositionGroup x
      · rw [h2]
  · have h : i_[L/K] ((restrictScalarsHom K) x) = i_[L/K'] x := rfl
    simp only [htop, ↓reduceDIte]
    by_cases hc : (WithTop.untop (FuncJ L σ) (FuncJ_untop_of_nerefl σ hsig)) ≤ (WithTop.untop ( i_[L/K'] x) (of_eq_false (eq_false htop)))
    · rw [min_eq_left]
      apply le_antisymm
      · norm_cast
        apply (WithTop.le_untop_iff _).2
        simp only [WithTop.coe_untop]
        apply preimage_lowerIndex_le_FuncJ σ
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1
        simp only [_root_.map_mul, h1, restrictNormalHom_restrictScalarsHom, one_mul]
      · norm_cast
        apply (WithTop.le_untop_iff _).2
        simp only [WithTop.coe_untop]
        apply le_trans _ (lowerIndex_inf_le_mul _ _ hgen)
        apply le_min_iff.2
        constructor
        ·
          --rw [← WithTop.coe_untop (FuncJ L σ ) (FuncJ_untop_of_nerefl σ hsig), ← WithTop.coe_untop (i_[L/K] ((restrictScalarsHom K) x)) (of_eq_false (eq_false htop))]
          rw [h]
          by_contra hc'
          absurd hc
          push_neg at hc' ⊢
          apply (WithTop.lt_untop_iff _).2
          simp only [WithTop.coe_untop]
          exact hc'
        · rw [h2]
      norm_cast
    · rw [min_eq_right]
      norm_cast
      apply le_antisymm
      · apply (WithTop.le_untop_iff _).2
        simp only [WithTop.coe_untop, ← h]
        push_neg at hc
        apply lowerIndex_mul_le σ hsig h2 htop hc hgen
      · apply (WithTop.le_untop_iff _).2
        simp only [WithTop.coe_untop]
        apply le_trans _ (lowerIndex_inf_le_mul _ _ hgen)
        rw [h, min_eq_left]
        rw [h2]
        by_contra hc'
        absurd hc
        push_neg at hc'
        apply (WithTop.le_untop_iff _).2
        simp only [WithTop.coe_untop]
        apply le_of_lt hc'
      norm_cast
      push_neg at hc
      apply le_of_lt hc

#check Ideal.ramificationIdx_ne_zero
theorem lowerIndex_eq_phi_FuncJ_of_ne_refl (hsig : σ ≠ .refl) (x : PowerBasis 𝒪[K] 𝒪[L]) (y : PowerBasis 𝒪[K'] 𝒪[L]) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : (lowerIndex K K' σ).untop (lowerIndex_ne_one (mem_decompositionGroup σ) hsig) = phi K' L ((FuncJ L σ).untop ((FuncJ_untop_of_nerefl σ hsig)) - 1) + 1 := by
  obtain ⟨s, hs1, hs2⟩ := preimage_lowerIndex_eq_FuncJ (K' := K') (L := L) σ hsig
  suffices h : (LocalField.ramificationIdx K' L) * (lowerIndex K K' σ).untop (lowerIndex_ne_one (mem_decompositionGroup σ) hsig) = (LocalField.ramificationIdx K' L) * (phi K' L ((FuncJ L σ).untop (FuncJ_untop_of_nerefl σ hsig) - 1) + 1) from by
    apply mul_left_cancel₀ at h
    exact h
    norm_cast
    apply ramificationIdx_ne_zero
  rw [← Nat.cast_mul, prop3_aux (K := K) (K' := K') (L := L) σ hsig hs1 x y, phi_eq_sum_inf, RamificationIdx_eq_card_of_inertia_group, sub_add_cancel, ← mul_assoc, mul_one_div_cancel, one_mul, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [sub_add_cancel]
  apply lowerIndex_eq_inf σ hsig hs1 hs2 hgen
  norm_cast
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

theorem truncatedJ_eq_trunc_iff_lowerIdx_le_phi {u : ℚ} (hsig : σ ≠ .refl) (x : PowerBasis 𝒪[K] 𝒪[L]) (y : PowerBasis 𝒪[K'] 𝒪[L]) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : min (phi K' L u + 1) ((i_[K'/K] σ).untop (lowerIndex_ne_one (mem_decompositionGroup σ) hsig)) = phi K' L u + 1 ↔ truncatedJ L (u + 1) σ = u := by
  constructor
  · intro hu
    simp only [truncatedJ_eq_truncated_FuncJ, (FuncJ_untop_of_nerefl σ hsig), ↓reduceDIte]
    rw [min_eq_right]
    simp only [add_sub_cancel_right]
    suffices h : phi K' L u ≤ phi K' L ((FuncJ L σ).untop (FuncJ_untop_of_nerefl σ hsig) - 1) from by
      linarith [(StrictMono.le_iff_le (phi_strictMono K' L)).1 h]
    rw [← add_le_add_iff_right (a := 1), ← lowerIndex_eq_phi_FuncJ_of_ne_refl σ hsig x y hgen, ← hu]
    apply min_le_right
  · intro hu
    rw [min_eq_left]
    simp only [truncatedJ_eq_truncated_FuncJ, (FuncJ_untop_of_nerefl σ hsig), ↓reduceDIte] at hu
    rw [lowerIndex_eq_phi_FuncJ_of_ne_refl (L := L) σ hsig x y hgen, add_le_add_iff_right]
    apply (phi_strictMono K' L).monotone
    rw [← hu]
    simp only [tsub_le_iff_right, sub_add_cancel, min_le_iff, le_refl, true_or]

theorem lemma3_aux' (u : ℚ) (x : PowerBasis 𝒪[K] 𝒪[L]) (y : PowerBasis 𝒪[K'] 𝒪[L]) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : σ.truncatedLowerIndex K K' (phi K' L u + 1) = (1 / LocalField.ramificationIdx K' L) * (∑ s in (⊤ : Finset (L ≃ₐ[K'] L)), (AlgEquiv.truncatedLowerIndex K L (truncatedJ L (u + 1) σ + 1) (AlgEquiv.restrictScalars K s))) := by
  by_cases hsig : σ = .refl
  · conv =>
      left
      simp only [hsig, truncatedLowerIndex, lowerIndex_refl, ↓reduceDIte, one_div, Finset.top_eq_univ, lowerIndex_restrictScalars]
    conv =>
      right
      simp only [hsig, truncatedJ_refl]
    rw [phi_eq_sum_inf K' L, RamificationIdx_eq_card_of_inertia_group]
    simp only [sub_add_cancel, truncatedLowerIndex_restrictScalars]
  · have h : ¬ lowerIndex K K' σ = ⊤ := by
      apply lowerIndex_ne_one ?_ hsig
      apply mem_decompositionGroup σ
    conv =>
      left
      simp only [truncatedLowerIndex, h, ↓reduceDIte]
    have hunion : (⊤ : Finset (L ≃ₐ[K'] L)) = ((⊤ \ {.refl}) : Finset (L ≃ₐ[K'] L)) ∪ ({.refl} : Finset (L ≃ₐ[K'] L)) := by
      simp only [Finset.top_eq_univ, Finset.sdiff_union_self_eq_union, Finset.left_eq_union, Finset.subset_univ]
    have hrefl : ∑ x ∈ ({.refl} : Finset (L ≃ₐ[K'] L)), i_[L/K]ₜ (truncatedJ L (u + 1) σ + 1) (restrictScalars K x) = truncatedJ L (u + 1) σ + 1 := by
      simp only [truncatedLowerIndex_restrictScalars, Finset.sum_singleton, truncatedLowerIndex_refl]
    rw [hunion, Finset.sum_union, hrefl]
    by_cases hu : min (phi K' L u + 1) ↑(WithTop.untop ( i_[K'/K] σ) h) = phi K' L u + 1
    · have hu' : truncatedJ L (u + 1) σ = u := by
        apply (truncatedJ_eq_trunc_iff_lowerIdx_le_phi (K := K) (K' := K') (L := L) σ hsig x y hgen).1 hu
      rw [hu, hu', phi_eq_sum_inf, RamificationIdx_eq_card_of_inertia_group]
      simp only [one_div, Finset.top_eq_univ, sub_add_cancel, truncatedLowerIndex_restrictScalars, Finset.subset_univ, Finset.sum_sdiff_eq_sub, Finset.sum_singleton, truncatedLowerIndex_refl]
    · have hu' : truncatedJ L (u + 1) σ = ((WithTop.untop (FuncJ L σ) (FuncJ_untop_of_nerefl σ hsig))) - 1 := by
        suffices h : ¬ truncatedJ L (u + 1) σ = u from by
          simp only [truncatedJ_eq_truncated_FuncJ, FuncJ_untop_of_nerefl σ hsig, ↓reduceDIte, add_sub_cancel_right] at h ⊢
          rw [min_eq_left]
          by_contra hc
          push_neg at hc
          absurd h
          rw [sub_eq_of_eq_add]
          apply min_eq_right (le_of_lt hc)
        by_contra hc
        absurd hu
        apply (truncatedJ_eq_trunc_iff_lowerIdx_le_phi (K := K) (K' := K') (L := L) σ hsig x y hgen).2 hc
      simp only [Classical.or_iff_not_imp_left.1 (min_choice (phi K' L u + 1) (↑(WithTop.untop ( i_[K'/K] σ) h))) hu, hu']
      rw [lowerIndex_eq_phi_FuncJ_of_ne_refl (L := L) σ hsig x y hgen, phi_eq_sum_inf, RamificationIdx_eq_card_of_inertia_group, sub_add_cancel]
      simp only [one_div, Finset.top_eq_univ, truncatedLowerIndex_restrictScalars, Finset.subset_univ, Finset.sum_sdiff_eq_sub, Finset.sum_singleton, truncatedLowerIndex_refl, sub_add_cancel]
    exact Finset.sdiff_disjoint
