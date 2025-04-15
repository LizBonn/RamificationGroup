import RamificationGroup.LowerNumbering.prop_3
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import RamificationGroup.HerbrandFunction.Psi
import RamificationGroup.ForMathlib.AlgEquiv.Basic
import RamificationGroup.ForMathlib.Unknow
-- import RamificationGroup.Valued.Hom.Discrete'

/-!

## TODO
rename theorems into UpperRamificationGroup.xxx
-/

open QuotientGroup IntermediateField DiscreteValuation Valued Valuation HerbrandFunction Classical AlgEquiv

noncomputable
section

section upperRamificationGroup_aux

section definition_aux
-- principle : first try to state a theorem in IsScalarTower, then try IntermediateField
variable {K L : Type*} {ΓK : outParam Type*} [Field K] [Field L] [LinearOrderedCommGroupWithZero ΓK] [vK : Valued K ΓK] [vL : Valued L ℤₘ₀] [Algebra K L]

variable {K' : Type*} [Field K'] [vK' : Valued K' ℤₘ₀] [Algebra K K'] [Algebra K L] [Algebra K' L] [IsScalarTower K K' L] [IsValExtension vK'.v vL.v] -- `I hope this is enough`

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [Algebra R S]

-- aux construction of upper numbering ramification group, correct for finite extension of local fields only. later we define a more general version on all algebraic extensions of local fields.

def upperRamificationGroup_aux (v : ℚ): (Subgroup (S ≃ₐ[R] S)) := lowerRamificationGroup R S ⌈psi R S v⌉

end definition_aux

local notation:max " G(" L:max "/" K:max ")^[" v:max "] " => upperRamificationGroup_aux K L v

section autCongr

variable {K L L': Type*} {ΓK : outParam Type*} [Field K] [Field L] [Field L'] [vL : Valued L ℤₘ₀] [vL' : Valued L' ℤₘ₀] [IsDiscrete vL.v] [IsDiscrete vL'.v] [Algebra K L] [Algebra K L']

theorem autCongr_mem_upperRamificationGroup_aux_iff {f : L ≃ₐ[K] L'} (hf : ∀ a : L, v a = v (f a)) (s : L ≃ₐ[K] L) (v : ℚ) : s ∈ G(L/K)^[v] ↔ (AlgEquiv.autCongr f s : L' ≃ₐ[K] L') ∈ G(L'/K)^[v] := by
  convert autCongr_mem_lowerRamificationGroup_iff hf s ⌈psi K L v⌉
  simp only [upperRamificationGroup_aux]
  congr 2
  exact (psi_eq_ofEquiv _ _ _ hf v).symm

end autCongr

variable {K K' L : Type*} {ΓK : outParam Type*} [Field K] [Field K'] [Field L] [vK' : Valued K' ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK'.v] [IsDiscrete vL.v] [Algebra K L] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L] [IsValExtension vK'.v vL.v] [Normal K K'] [Normal K L] [FiniteDimensional K L] [FiniteDimensional K K'] [FiniteDimensional K' L]

variable [vK : Valued K ℤₘ₀] [IsDiscrete vK.v] [CompleteSpace K] [IsValExtension vK.v vK'.v] [IsValExtension vK.v vL.v]


variable (σ : K' ≃ₐ[K] K')

variable (L) in
def HerbrandFunction.FuncJ (σ : K' ≃ₐ[K] K') : ℕ∞ := Finset.max' (((AlgEquiv.restrictNormalHom K')⁻¹' {σ}).toFinset.image (fun (x : L ≃ₐ[K] L) => AlgEquiv.lowerIndex K L x)) (Finset.Nonempty.image preimage_singleton_nonempty _)

variable (L) in
def HerbrandFunction.truncatedJ (u : ℚ) (σ : K' ≃ₐ[K] K') : ℚ := Finset.max' (((AlgEquiv.restrictNormalHom K')⁻¹' {σ}).toFinset.image (fun (x : L ≃ₐ[K] L) => x.truncatedLowerIndex K L u - 1)) (Finset.Nonempty.image preimage_singleton_nonempty _)

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

omit vK' [vK'.v.IsDiscrete] [IsValExtension vK'.v vL.v] [FiniteDimensional K K'] [FiniteDimensional K' L] in
theorem exist_truncatedLowerIndex_eq_truncatedJ (u : ℚ) (σ : K' ≃ₐ[K] K') : ∃ s : L ≃ₐ[K] L, s ∈ (AlgEquiv.restrictNormalHom K')⁻¹' {σ} ∧  AlgEquiv.truncatedLowerIndex K L u s - 1 = HerbrandFunction.truncatedJ L u σ := by
  have hnem : ((AlgEquiv.restrictNormalHom K' (K₁ := L))⁻¹' {σ}).Nonempty := by
    have h1 : Set.SurjOn (AlgEquiv.restrictNormalHom K' (K₁ := L)) ((AlgEquiv.restrictNormalHom K' (K₁ := L))⁻¹' {σ}) {σ} := by
      simp only [Set.surjOn_singleton, Set.mem_image, Set.mem_preimage, Set.mem_singleton_iff, and_self]
      apply AlgEquiv.restrictNormalHom_surjective
    apply Set.SurjOn.comap_nonempty h1 (by simp)
  have hfin : Finite ((AlgEquiv.restrictNormalHom K' (K₁ := L))⁻¹' {σ}) := by
    have hfin' : (⊤ : Set (L ≃ₐ[K] L)).Finite := by
      exact Set.toFinite ⊤
    apply Set.Finite.subset hfin' (by simp only [Set.top_eq_univ, Set.subset_univ])
  obtain ⟨s, hs⟩ := Set.exists_max_image ((AlgEquiv.restrictNormalHom K' (K₁ := L))⁻¹' {σ}) (fun x => AlgEquiv.truncatedLowerIndex K L u x - 1) hfin hnem
  use s
  rcases hs with ⟨hs1, hs2⟩
  constructor
  · exact hs1
  · unfold truncatedJ
    apply le_antisymm
    · apply Finset.le_max'
      apply Finset.mem_image.2
      use s
      constructor
      apply Set.mem_toFinset.2 hs1; rfl
    · have hnem' : (((AlgEquiv.restrictNormalHom K')⁻¹' {σ}).toFinset.image (fun (x : L ≃ₐ[K] L) => x.truncatedLowerIndex K L u - 1)).Nonempty := by
        apply Finset.Nonempty.image
        apply Set.toFinset_nonempty.2 hnem
      apply (Finset.max'_le_iff (((AlgEquiv.restrictNormalHom K')⁻¹' {σ}).toFinset.image (fun (x : L ≃ₐ[K] L) => x.truncatedLowerIndex K L u - 1)) hnem').2
      intro y hy
      have hy1 : ∃ b ∈ (AlgEquiv.restrictNormalHom K') ⁻¹' {σ}, i_[L/K]ₜ u b - 1 = y := by
        convert Finset.mem_image.1 hy
        ext
        apply Set.mem_toFinset.symm
      obtain ⟨b, hb1, hb2⟩ := hy1
      rw [← hb2]
      apply hs2
      exact hb1

theorem FuncJ_untop_of_nerefl [Algebra.IsSeparable K L] (h : σ ≠ .refl) : FuncJ L σ ≠ ⊤ := by
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

theorem FuncJ_untop_iff_nerefl [Algebra.IsSeparable K L] : σ ≠ .refl ↔ FuncJ L σ ≠ ⊤ := by
  constructor
  · exact fun a ↦ FuncJ_untop_of_nerefl σ a
  · intro h
    by_contra hc
    absurd h
    exact FuncJ_refl σ hc

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

theorem preimage_lowerIndex_le_FuncJ {a : L ≃ₐ[K] L} (ha : restrictNormalHom K' a = σ) : i_[L/K] a ≤ FuncJ L σ := by
  unfold FuncJ
  apply Finset.le_max'
  simp only [Finset.mem_image, Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]
  use a

variable [Algebra.IsSeparable K L]

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
      simp at hi hs
      have hs' : restrictNormalHom K' s⁻¹ = restrictNormalHom K' i.symm := by
        rw [MonoidHom.map_inv (restrictNormalHom K') s, hs, ← hi, ← MonoidHom.map_inv (restrictNormalHom K') i]
        exact rfl
      rw [← AlgEquiv.restrictNormal_commutes, ← AlgEquiv.restrictNormal_commutes, restrictNormal_restrictNormalHom s⁻¹, restrictNormal_restrictNormalHom, hs']
  }
  use x
  simp only [toEquiv_eq_coe, x]
  exact rfl

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

variable [Algebra.IsSeparable K K'] [Algebra.IsSeparable K' L][CompleteSpace K'] [Algebra.IsSeparable ↥𝒪[K'] ↥𝒪[L]] [Normal K' L] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] in
theorem prop3_aux (hsig : σ ≠ .refl) {s : L ≃ₐ[K] L} (h1 : s ∈ ((restrictNormalHom K')⁻¹' {σ})) (x : PowerBasis 𝒪[K] 𝒪[L]) (y : PowerBasis 𝒪[K] 𝒪[K']) : (LocalField.ramificationIdx K' L) * (lowerIndex K K' σ).untop (lowerIndex_ne_one (mem_decompositionGroup σ) hsig) = (∑ x : (L ≃ₐ[K'] L), (i_[L/K] ((restrictScalarsHom K x) * s)).untop (preimage_untop σ hsig h1)) := by
  calc
    _ = ((LocalField.ramificationIdx K' L) * (lowerIndex K K' σ)).untop ?_ := by
      rw [← WithTop.coe_eq_coe, WithTop.coe_mul, WithTop.coe_untop, WithTop.coe_untop]
      rfl
      apply ne_of_lt (WithTop.mul_lt_top _ _)
    _ = (∑ x : ((restrictNormalHom K' (K₁ := L))⁻¹' {σ}), i_[L/K] x).untop ?_:= by
      rw [← WithTop.coe_eq_coe, WithTop.coe_untop, WithTop.coe_untop, ← prop3 (K := K) (M := K') (L := L) σ x y]
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

variable [CompleteSpace K'] in
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
        · rw [h]
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

theorem RamificationIdx_eq_card_of_inertia_group : (Nat.card G(L/K')_[0]) = (LocalField.ramificationIdx K' L) := by
  simp only [lowerRamificationGroup, LocalField.ramificationIdx, IsLocalRing.ramificationIdx]
  sorry

set_option maxHeartbeats 0
variable [Algebra.IsSeparable K K'] [Algebra.IsSeparable K' L][CompleteSpace K'] [Algebra.IsSeparable ↥𝒪[K'] ↥𝒪[L]] [Normal K' L] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] in
theorem lowerIndex_eq_phi_FuncJ_of_ne_refl (hsig : σ ≠ .refl) (x : PowerBasis 𝒪[K] 𝒪[L]) (y : PowerBasis 𝒪[K] 𝒪[K']) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) {gen' : 𝒪[L]} (hgen' : Algebra.adjoin 𝒪[K'] {gen'} = ⊤) : (lowerIndex K K' σ).untop (lowerIndex_ne_one (mem_decompositionGroup σ) hsig) = phi K' L ((FuncJ L σ).untop ((FuncJ_untop_of_nerefl σ hsig)) - 1) + 1 := by
  obtain ⟨s, hs1, hs2⟩ := preimage_lowerIndex_eq_FuncJ (K' := K') (L := L) σ hsig
  suffices h : (LocalField.ramificationIdx K' L) * (lowerIndex K K' σ).untop (lowerIndex_ne_one (mem_decompositionGroup σ) hsig) = (LocalField.ramificationIdx K' L) * (phi K' L ((FuncJ L σ).untop (FuncJ_untop_of_nerefl σ hsig) - 1) + 1) from by
    apply mul_left_cancel₀ at h
    exact h
    norm_cast
    apply ramificationIdx_ne_zero
  rw [← Nat.cast_mul, prop3_aux (K := K) (K' := K') (L := L) σ hsig hs1 x y, phi_eq_sum_inf_aux K' L (hgen := hgen'), RamificationIdx_eq_card_of_inertia_group, sub_add_cancel, ← mul_assoc, mul_one_div_cancel, one_mul, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [sub_add_cancel]
  apply lowerIndex_eq_inf σ hsig hs1 hs2 hgen
  norm_cast
  apply ramificationIdx_ne_zero
  simp only [neg_le_sub_iff_le_add, le_add_iff_nonneg_left, Nat.cast_nonneg]

variable [Algebra.IsSeparable K K'] [Algebra.IsSeparable K' L] [CompleteSpace K'] [Algebra.IsSeparable ↥𝒪[K'] ↥𝒪[L]] [Normal K' L] in
variable [Algebra.IsSeparable K K'] [Algebra.IsSeparable K' L] [CompleteSpace K'] [Algebra.IsSeparable ↥𝒪[K'] ↥𝒪[L]] [Normal K' L] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable K K'] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] in
theorem truncatedJ_eq_trunc_iff_lowerIdx_le_phi {u : ℚ} (hsig : σ ≠ .refl) (x : PowerBasis 𝒪[K] 𝒪[L]) (y : PowerBasis 𝒪[K] 𝒪[K']) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) {gen' : 𝒪[L]} (hgen' : Algebra.adjoin 𝒪[K'] {gen'} = ⊤) : min (phi K' L u + 1) ((i_[K'/K] σ).untop (lowerIndex_ne_one (mem_decompositionGroup σ) hsig)) = phi K' L u + 1 ↔ truncatedJ L (u + 1) σ = u := by
  constructor
  · intro hu
    simp only [truncatedJ_eq_truncated_FuncJ, (FuncJ_untop_of_nerefl σ hsig), ↓reduceDIte]
    rw [min_eq_right]
    simp only [add_sub_cancel_right]
    suffices h : phi K' L u ≤ phi K' L ((FuncJ L σ).untop (FuncJ_untop_of_nerefl σ hsig) - 1) from by
      linarith [(StrictMono.le_iff_le (phi_strictMono K' L)).1 h]
    rw [← add_le_add_iff_right (a := 1), ← lowerIndex_eq_phi_FuncJ_of_ne_refl σ hsig x y hgen hgen', ← hu]
    apply min_le_right
  · intro hu
    rw [min_eq_left]
    simp only [truncatedJ_eq_truncated_FuncJ, (FuncJ_untop_of_nerefl σ hsig), ↓reduceDIte] at hu
    rw [lowerIndex_eq_phi_FuncJ_of_ne_refl (L := L) σ hsig x y hgen hgen', add_le_add_iff_right]
    apply (phi_strictMono K' L).monotone
    rw [← hu]
    simp only [tsub_le_iff_right, sub_add_cancel, min_le_iff, le_refl, true_or]


variable [Algebra.IsSeparable K K'] [Algebra.IsSeparable K' L] [CompleteSpace K'] [Algebra.IsSeparable ↥𝒪[K'] ↥𝒪[L]] [Normal K' L] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable K K'] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] in
theorem lemma3_aux' (u : ℚ) (h' : 0 ≤ u) (x : PowerBasis 𝒪[K] 𝒪[L]) (y : PowerBasis 𝒪[K] 𝒪[K']) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) {gen' : 𝒪[L]} (hgen' : Algebra.adjoin 𝒪[K'] {gen'} = ⊤) : σ.truncatedLowerIndex K K' (phi K' L u + 1) = (1 / LocalField.ramificationIdx K' L) * (∑ s in (⊤ : Finset (L ≃ₐ[K'] L)), (AlgEquiv.truncatedLowerIndex K L (truncatedJ L (u + 1) σ + 1) (AlgEquiv.restrictScalars K s))) := by
  by_cases hsig : σ = .refl
  · conv =>
      left
      simp only [hsig, truncatedLowerIndex, lowerIndex_refl, ↓reduceDIte, one_div, Finset.top_eq_univ, lowerIndex_restrictScalars]
    conv =>
      right
      simp only [hsig, truncatedJ_refl]
    rw [phi_eq_sum_inf_aux K' L _ (by linarith) hgen', RamificationIdx_eq_card_of_inertia_group]
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
        apply (truncatedJ_eq_trunc_iff_lowerIdx_le_phi (K := K) (K' := K') (L := L) σ hsig x y hgen hgen').1 hu
      rw [hu, hu', phi_eq_sum_inf_aux K' L _ (by linarith) hgen', RamificationIdx_eq_card_of_inertia_group]
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
        apply (truncatedJ_eq_trunc_iff_lowerIdx_le_phi (K := K) (K' := K') (L := L) σ hsig x y hgen hgen').2 hc
      simp only [Classical.or_iff_not_imp_left.1 (min_choice (phi K' L u + 1) (↑(WithTop.untop ( i_[K'/K] σ) h))) hu, hu']
      rw [lowerIndex_eq_phi_FuncJ_of_ne_refl (L := L) σ hsig x y hgen hgen', phi_eq_sum_inf_aux K' L _ _ hgen', RamificationIdx_eq_card_of_inertia_group, sub_add_cancel]
      simp only [one_div, Finset.top_eq_univ, truncatedLowerIndex_restrictScalars, Finset.subset_univ, Finset.sum_sdiff_eq_sub, Finset.sum_singleton, truncatedLowerIndex_refl, sub_add_cancel]
      simp only [neg_le_sub_iff_le_add, le_add_iff_nonneg_left, Nat.cast_nonneg]
    exact Finset.sdiff_disjoint

variable [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable K' L] [CompleteSpace K'] [Algebra.IsSeparable K K'] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[K'])] [Algebra.IsSeparable ↥𝒪[K'] ↥𝒪[L]] [Normal K' L] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])]

theorem phi_truncatedJ_sub_one (u : ℚ) (hu : 0 ≤ u) (x : PowerBasis 𝒪[K] 𝒪[L]) (y : PowerBasis 𝒪[K] 𝒪[K']) (σ : K' ≃ₐ[K] K') {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) {gen' : 𝒪[L]} (hgen' : Algebra.adjoin 𝒪[K'] {gen} = ⊤) : phi K' L (truncatedJ L (u + 1) σ) + 1 = σ.truncatedLowerIndex K K' ((phi K' L u) + 1) := by
  calc
  _ = (1 / Nat.card G(L/K')_[0]) * ((Finset.sum (⊤ : Finset (L ≃ₐ[K'] L)) (AlgEquiv.truncatedLowerIndex K' L (truncatedJ L (u + 1) σ + 1) ·))) := by
    rw [phi_eq_sum_inf_aux K' L _ _ hgen']
    simp
    unfold truncatedJ
    apply Finset.le_max'
    simp only [Finset.mem_image, Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, sub_eq_neg_self]
    repeat sorry
  _ = (1 / LocalField.ramificationIdx K' L) * ((Finset.sum (⊤ : Finset (L ≃ₐ[K'] L)) (AlgEquiv.truncatedLowerIndex K' L (truncatedJ L (u + 1) σ + 1) ·))) := by
    congr
    apply RamificationIdx_eq_card_of_inertia_group
  _ = (1 / LocalField.ramificationIdx K' L) * ((∑ x in (⊤ : Finset (L ≃ₐ[K'] L)), (AlgEquiv.truncatedLowerIndex K L (truncatedJ L (u + 1) σ + 1) (AlgEquiv.restrictScalars K x)))) := by
    congr
  _ = σ.truncatedLowerIndex K K' ((phi K' L u) + 1) := by
    rw [lemma3_aux' σ u hu x y hgen hgen']


theorem mem_lowerRamificationGroup_of_le_truncatedJ_sub_one {u r : ℚ} (h : u ≤ truncatedJ L r σ) {gen : ↥𝒪[L]} (hgen : Algebra.adjoin ↥𝒪[K] {gen} = ⊤) : σ ∈ (G(L/K)_[⌈u⌉].map (AlgEquiv.restrictNormalHom K')) := by
  simp only [Subgroup.mem_map]
  obtain ⟨s, s_in, hs⟩ := exist_truncatedLowerIndex_eq_truncatedJ (L := L) r σ
  simp at s_in
  have hs : s ∈ G(L/K)_[⌈u⌉] := by
    apply mem_lowerRamificationGroup_of_le_truncatedLowerIndex_sub_one (r := r) ?_ hgen
    rw [hs]
    linarith [h]
    rw [decompositionGroup_eq_top]
    apply Subgroup.mem_top
  use s

theorem le_truncatedJ_sub_one_iff_mem_lowerRamificationGroup {u : ℚ} {r : ℚ} (h : u + 1 ≤ r) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : u ≤ truncatedJ L r σ ↔ σ ∈ (G(L/K)_[⌈u⌉].map (AlgEquiv.restrictNormalHom K')) := by
  constructor
  · intro hu
    apply mem_lowerRamificationGroup_of_le_truncatedJ_sub_one _ hu hgen
  · rintro hx
    obtain ⟨s, s_in, hs⟩ := exist_truncatedLowerIndex_eq_truncatedJ (L := L) r σ
    simp at s_in
    have hs' : s ∈ G(L/K)_[⌈u⌉] := by
      obtain ⟨k, hk1, hk2⟩ := Subgroup.mem_map.1 hx
      have h1 : i_[L/K]ₜ r k - 1 ≤ i_[L/K]ₜ r s - 1 := by
        have h1' : k ∈ (⇑(AlgEquiv.restrictNormalHom K') ⁻¹' {σ}) := by simp only [Set.mem_preimage,
          hk2, Set.mem_singleton_iff]
        rw [hs]
        unfold truncatedJ
        apply Finset.le_max'
        rw [Finset.mem_image]
        use k
        constructor
        · simp only [Set.mem_toFinset, h1']
        · rfl
      have h2 : u ≤ i_[L/K]ₜ r k - 1 := by
        apply (le_truncatedLowerIndex_sub_one_iff_mem_lowerRamificationGroup _ _ _ h hgen).2 hk1
      have h3 : u ≤ i_[L/K]ₜ r s - 1 := by linarith [h1, h2]
      apply mem_lowerRamificationGroup_of_le_truncatedLowerIndex_sub_one ?_ hgen h3
      rw [decompositionGroup_eq_top]
      apply Subgroup.mem_top
    rw [← hs]
    apply (le_truncatedLowerIndex_sub_one_iff_mem_lowerRamificationGroup s u r h hgen).2 hs'

variable [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable K L] [Algebra.IsSeparable K K'] [Algebra.IsSeparable K' L] [CompleteSpace K'] [CompleteSpace K] [Normal K' L] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] in
@[simp]
theorem herbrand (u : ℚ) {gen : 𝒪[K']} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) {gen' : 𝒪[L]} (hgen' : Algebra.adjoin 𝒪[K] {gen'} = ⊤) : G(L/K)_[⌈u⌉].map (AlgEquiv.restrictNormalHom K') = G(K'/K)_[⌈phi K' L u⌉] := by
  ext σ
  calc
  _ ↔ truncatedJ L (u + 1) σ ≥ u :=
    (le_truncatedJ_sub_one_iff_mem_lowerRamificationGroup σ (by linarith) hgen').symm
  _ ↔ phi K' L (truncatedJ L (u + 1) σ) ≥ phi K' L u := (phi_strictMono K' L).le_iff_le.symm
  _ ↔ σ.truncatedLowerIndex K K' (phi K' L u + 1) - 1 ≥ phi K' L u := by
    have heq : phi K' L (truncatedJ L (u + 1) σ) + 1 = i_[K'/K]ₜ (phi K' L u + 1) σ := by sorry
      -- simp only [phi_truncatedJ_sub_one]
    have heq' : phi K' L (truncatedJ L (u + 1) σ) = i_[K'/K]ₜ (phi K' L u + 1) σ - 1 := by
      linarith [heq]
    rw [heq']
  _ ↔ σ ∈ G(K'/K)_[⌈phi K' L u⌉] := by
    apply le_truncatedLowerIndex_sub_one_iff_mem_lowerRamificationGroup (K := K) (L := K') σ (phi K' L u) _ ?_ hgen
    linarith
