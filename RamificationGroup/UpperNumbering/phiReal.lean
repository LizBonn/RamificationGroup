import RamificationGroup.UpperNumbering.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import RamificationGroup.Valuation.Extension

open QuotientGroup IntermediateField DiscreteValuation Valued Valuation HerbrandFunction MeasureTheory.MeasureSpace intervalIntegral Pointwise AlgEquiv ExtDVR Asymptotics Filter intervalIntegral MeasureTheory

variable (K K' L : Type*) {ΓK : outParam Type*} [Field K] [Field K'] [Field L] [vK : Valued K ℤₘ₀] [vK' : Valued K' ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK.v] [IsDiscrete vK'.v] [IsDiscrete vL.v] [Algebra K L] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L] [IsValExtension vK.v vK'.v] [IsValExtension vK'.v vL.v] [IsValExtension vK.v vL.v] [Normal K K'] [Normal K L] [FiniteDimensional K L] [FiniteDimensional K K'] [FiniteDimensional K' L]

local notation:max " G(" L:max "/" K:max ")^[" v:max "] " => upperRamificationGroup_aux K L v

noncomputable def μ : MeasureTheory.Measure ℝ := MeasureTheory.volume

noncomputable def phiDerivReal (u : ℝ) : ℝ :=
  (Nat.card G(L/K)_[(max 0 ⌈u⌉)] : ℝ) / (Nat.card G(L/K)_[0] : ℝ)

noncomputable def phiReal (u : Real) : Real := ∫ x in (0 : ℝ)..u, phiDerivReal K L x ∂μ

theorem phiReal_zero_eq_zero : phiReal K L 0 = 0 := by
  unfold phiReal
  simp only [intervalIntegral.integral_same]


theorem phiReal_one_le_one : phiReal K L 1 ≤ 1 := by
  unfold phiReal
  rw [integral_of_le, MeasureTheory.setIntegral_congr_fun (g := fun x => phiDerivReal K L 1) measurableSet_Ioc, MeasureTheory.setIntegral_const]
  simp only [not_lt, zero_le_one, Set.Ioc_eq_empty, MeasureTheory.measure_empty, ENNReal.zero_toReal, sub_zero, smul_eq_mul, μ, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, ENNReal.one_toReal, one_mul, phiDerivReal]
  apply (div_le_one _).2
  rw [Nat.cast_le]
  apply Nat.card_mono
  exact Set.toFinite (G(L/K)_[0] : Set (L ≃ₐ[K] L))
  simp only [Int.ceil_one, zero_le_one, max_eq_right, SetLike.coe_subset_coe]
  apply lowerRamificationGroup.antitone K L (by linarith)
  simp only [Nat.cast_pos, Nat.card_pos]
  intro x hx
  unfold phiDerivReal
  have hx' : ⌈x⌉ = ⌈(1 : ℝ)⌉ := by
    simp only [Int.ceil_one, Int.ceil_eq_iff, Int.cast_one, sub_self]
    refine ⟨(Set.mem_Ioc.1 hx).1, (Set.mem_Ioc.1 hx).2⟩
  rw [hx']
  linarith

theorem phiDerivReal_pos {x : ℝ} : 0 < phiDerivReal K L x := by
  unfold phiDerivReal
  apply div_pos
  · by_cases hc : 0 ≤ x
    · rw [max_eq_right (Int.ceil_nonneg hc), Nat.cast_pos]
      convert Ramification_Group_card_pos K L (u := ⌈x⌉)
      exact Eq.symm (Int.ceil_intCast ⌈x⌉)
    · rw [max_eq_left, Nat.cast_pos, ← Int.ceil_zero (α := ℤ)]
      apply Ramification_Group_card_pos K L (u := 0)
      apply Int.ceil_le.2
      apply le_of_lt
      push_neg at hc
      rw [Int.cast_zero]
      exact hc
  · rw [Nat.cast_pos, ← Int.ceil_zero (α := ℤ)]
    apply Ramification_Group_card_pos K L (u := 0)

theorem phiDerivReal_le_one {u : ℝ} (h : 0 < u) : phiDerivReal K L u ≤ 1 := by
  have h' : 0 ≤ ⌈u⌉ := le_of_lt (Int.ceil_pos.2 h)
  rw [phiDerivReal, max_eq_right, div_le_one, Nat.cast_le]
  apply Nat.card_mono
  exact Set.toFinite (G(L/K)_[0] : Set (L ≃ₐ[K] L))
  apply lowerRamificationGroup.antitone
  exact h'
  simp only [Nat.cast_pos, Nat.card_pos]
  exact h'

theorem phiReal_nonneg {u : ℝ} (h : 0 ≤ u) : 0 ≤ phiReal K L u := by
  simp only [phiReal, integral_of_le h]
  apply MeasureTheory.setIntegral_nonneg_ae measurableSet_Ioc
  unfold Filter.Eventually phiDerivReal
  apply MeasureTheory.ae_of_all
  intro a _
  apply div_nonneg
  apply Nat.cast_nonneg
  apply Nat.cast_nonneg

--------------------------------for lower
instance {u : ℤ} : Subgroup.Normal (lowerRamificationGroup K L u) := sorry


------------------------------for lower
theorem lowerIndex_eq_of_subgroup_aux {t : L ≃ₐ[K] L} {k : L ≃ₐ[K'] L} (h : AlgEquiv.restrictScalarsHom K k = t) : i_[L/K] t = i_[L/K'] k := by
  unfold AlgEquiv.lowerIndex
  have h' : ∀ x : L, t x = k x := by
    intro x
    rw [← h]
    rfl
  have h'' : ⨆ x : vL.v.integer, vL.v (t x - x) = ⨆ x : vL.v.integer, vL.v (k x - x) := iSup_congr fun i ↦ congrArg (vL.v) (congrFun (congrArg HSub.hSub (h' ↑i)) (i : L))
  rw [h'']

variable [CompleteSpace K] [CompleteSpace K']
theorem RamificationGroup_of_Subgroup_aux {t : L ≃ₐ[K] L} {n : ℤ} (hn : 0 ≤ n) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) {gen' : 𝒪[L]} (hgen' : Algebra.adjoin 𝒪[K'] {gen'} = ⊤) : t ∈ G(L/K')_[n].map (AlgEquiv.restrictScalarsHom K) → t ∈ G(L/K)_[n] := by
  intro ht
  rw [← Int.toNat_of_nonneg (a := n)]
  apply (mem_lowerRamificationGroup_iff_of_generator (K := K) (L := L) hgen ?_ n.toNat).2
  obtain ⟨k, hk1, hk2⟩ := Subgroup.mem_map.1 ht
  rw [lowerIndex_eq_of_subgroup_aux K K' L hk2]
  apply (mem_lowerRamificationGroup_iff_of_generator (K := K') (L := L) hgen' ?_ n.toNat).1
  rw [Int.toNat_of_nonneg]
  exact hk1
  apply hn
  repeat
    {
      rw [decompositionGroup_eq_top]
      exact trivial
    }
  apply hn

theorem RamificationGroup_iff_Subgroup_aux {t : L ≃ₐ[K] L} {n : ℤ} (hn : 0 ≤ n) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) {gen' : 𝒪[L]} (hgen' : Algebra.adjoin 𝒪[K'] {gen'} = ⊤) : t ∈ G(L/K')_[n].map (AlgEquiv.restrictScalarsHom K) ↔ t ∈ G(L/K)_[n] ⊓ (⊤ : Subgroup (L ≃ₐ[K'] L)).map (restrictScalarsHom K) := by
  constructor
  <;> intro ht
  · rw [Subgroup.mem_inf]
    constructor
    · apply RamificationGroup_of_Subgroup_aux K K' L hn hgen hgen' ht
    · obtain ⟨k, _, hk2⟩ := Subgroup.mem_map.1 ht
      apply Subgroup.mem_map.2
      use k
      constructor
      · apply Subgroup.mem_top
      · apply hk2
  · rw [Subgroup.mem_inf] at ht
    obtain ⟨k, _, hk2⟩ := Subgroup.mem_map.1 ht.2
    apply Subgroup.mem_map.2
    use k
    constructor
    · have h : k ∈ G(L/K')_[n.toNat] := by
        apply (mem_lowerRamificationGroup_iff_of_generator (K := K') (L := L) hgen' ?_ n.toNat).2
        rw [← lowerIndex_eq_of_subgroup_aux K K' L hk2]
        apply (mem_lowerRamificationGroup_iff_of_generator (K := K) (L := L) hgen ?_ n.toNat).1
        rw [Int.toNat_of_nonneg]
        exact ht.1
        apply hn
        repeat
          {
            rw [decompositionGroup_eq_top]
            exact trivial
          }
      rw [Int.toNat_of_nonneg] at h
      exact h
      apply hn
    · apply hk2

theorem RamificationGroup_card_comp_aux {x : ℝ} (hx : 0 ≤ x) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) {gen' : 𝒪[L]} (hgen' : Algebra.adjoin 𝒪[K'] {gen'} = ⊤) : (Nat.card (Subgroup.map (AlgEquiv.restrictNormalHom K') G(L/K)_[⌈x⌉]) : ℝ) * (Nat.card G(L/K')_[⌈x⌉] : ℝ) = (Nat.card G(L/K)_[⌈x⌉] : ℝ) := by
  norm_cast
  haveI h1 : G(L/K')_[⌈x⌉] ≃ (G(L/K')_[⌈x⌉].map (AlgEquiv.restrictScalarsHom K)) := by
    let f : G(L/K')_[⌈x⌉] → (G(L/K')_[⌈x⌉].map (AlgEquiv.restrictScalarsHom K)) := (fun t => ⟨ (AlgEquiv.restrictScalarsHom K) t.1,by exact Subgroup.apply_coe_mem_map (AlgEquiv.restrictScalarsHom K) G(L/K')_[⌈x⌉] t⟩)
    apply Equiv.ofBijective f
    constructor
    · intro x y
      dsimp [f]
      rw [Subtype.mk.injEq]
      intro hx
      apply_mod_cast AlgEquiv.restrictScalarsHom_injective K hx
    · intro t
      have ht : t.1 ∈ (Subgroup.map (AlgEquiv.restrictScalarsHom K) G(L/K')_[⌈x⌉] ) := by exact SetLike.coe_mem t
      obtain ⟨y, hy1, hy2⟩ := Subgroup.mem_map.1 ht
      dsimp [f]
      simp only [Subtype.exists]
      use y
      use hy1
      exact SetCoe.ext hy2
  haveI h2: (Subgroup.map (AlgEquiv.restrictNormalHom K') G(L/K)_[⌈x⌉]) ≃ (G(L/K)_[⌈x⌉] ⧸ (G(L/K)_[⌈x⌉] ⊓ (AlgEquiv.restrictNormalHom K').ker).subgroupOf G(L/K)_[⌈x⌉]) := by
    apply Subgroup_map
    -- exact AlgEquiv.restrictNormalHom_surjective L
  haveI h3 : (G(L/K')_[⌈x⌉].map (AlgEquiv.restrictScalarsHom K)) = (G(L/K)_[⌈x⌉] ⊓ (AlgEquiv.restrictNormalHom K').ker) := by
    ext t
    constructor
    <;> intro ht
    · apply Subgroup.mem_inf.2
      constructor
      · rw [(RamificationGroup_iff_Subgroup_aux K K' L ?_ hgen hgen'), Subgroup.mem_inf] at ht
        apply ht.1
        apply Int.ceil_nonneg hx
      · apply (MonoidHom.mem_ker (f := AlgEquiv.restrictNormalHom K')).2
        obtain ⟨y, _, hy2⟩ := Subgroup.mem_map.1 ht
        rw [← hy2]
        apply AlgEquiv.restrictNormalHom_restrictScalarsHom
    · rw [AlgEquiv.restrictNormal_ker_eq] at ht
      apply (RamificationGroup_iff_Subgroup_aux K K' L ?_ hgen hgen').2 ht
      apply Int.ceil_nonneg hx
  rw [Nat.card_congr h1, Nat.card_congr h2, h3]
  have h4 : Nat.card (↥ G(L/K)_[⌈x⌉] ⧸ ( G(L/K)_[⌈x⌉] ⊓ (AlgEquiv.restrictNormalHom K').ker).subgroupOf G(L/K)_[⌈x⌉] ) * Nat.card ((G(L/K)_[⌈x⌉] ⊓ (AlgEquiv.restrictNormalHom K').ker).subgroupOf G(L/K)_[⌈x⌉])= Nat.card (G(L/K)_[⌈x⌉]) := by
    symm
    apply Subgroup.card_eq_card_quotient_mul_card_subgroup
  rw [← h4]
  congr 1
  rw [Nat.card_congr]
  let f : (G(L/K)_[⌈x⌉] ⊓ (AlgEquiv.restrictNormalHom K').ker).subgroupOf G(L/K)_[⌈x⌉] → (G(L/K)_[⌈x⌉] ⊓ (AlgEquiv.restrictNormalHom K').ker : Subgroup (L ≃ₐ[K] L)) := fun x => ⟨x.1, by
    apply Subgroup.mem_subgroupOf.1
    exact SetLike.coe_mem x⟩
  haveI hf : Function.Bijective f := by
    constructor
    · intro x y
      dsimp [f]
      simp only [Subtype.mk.injEq, SetLike.coe_eq_coe, imp_self]
    · intro y
      dsimp [f]
      simp only [Subtype.exists]
      use y
      have hy1 : y.1 ∈ G(L/K)_[⌈x⌉] := by
        apply (Subgroup.mem_inf.1 (SetLike.coe_mem y)).1
      have hy2 : ⟨y.1, hy1⟩ ∈ ( G(L/K)_[⌈x⌉] ⊓ (AlgEquiv.restrictNormalHom K').ker).subgroupOf G(L/K)_[⌈x⌉] := by
        apply Subgroup.mem_subgroupOf.2
        simp only [SetLike.coe_mem]
      use hy1; use hy2
  symm
  apply Equiv.ofBijective f hf


variable [IsScalarTower 𝒪[K] 𝒪[K'] 𝒪[L]] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[K'])] in
theorem RamificationGroup_card_zero_comp_aux : (Nat.card G(K'/K)_[0] : ℝ) * (Nat.card G(L/K')_[0] : ℝ) = (Nat.card G(L/K)_[0] : ℝ) := by
  repeat rw [RamificationIdx_eq_card_of_inertia_group]
  norm_cast
  unfold LocalField.ramificationIdx IsLocalRing.ramificationIdx
  let e_K'K := Ideal.ramificationIdx (algebraMap ↥𝒪[K] ↥𝒪[K']) (IsLocalRing.maximalIdeal ↥𝒪[K]) (IsLocalRing.maximalIdeal ↥𝒪[K'])
  let e_LK' := Ideal.ramificationIdx (algebraMap ↥𝒪[K'] ↥𝒪[L]) (IsLocalRing.maximalIdeal ↥𝒪[K']) (IsLocalRing.maximalIdeal ↥𝒪[L])
  let e_LK := Ideal.ramificationIdx (algebraMap ↥𝒪[K] ↥𝒪[L]) (IsLocalRing.maximalIdeal ↥𝒪[K]) (IsLocalRing.maximalIdeal ↥𝒪[L])
  have h : (IsLocalRing.maximalIdeal 𝒪[L]) ^ (e_K'K * e_LK') = (IsLocalRing.maximalIdeal 𝒪[L]) ^ (e_LK) := by
    dsimp [e_K'K, e_LK', e_LK]
    rw [← maximalIdeal_map_eq_maximalIdeal_pow_ramificationIdx (IsValExtension.integerAlgebra_injective K L), mul_comm, pow_mul, ← maximalIdeal_map_eq_maximalIdeal_pow_ramificationIdx (IsValExtension.integerAlgebra_injective K' L), ← Ideal.map_pow, ← maximalIdeal_map_eq_maximalIdeal_pow_ramificationIdx (IsValExtension.integerAlgebra_injective K K'), Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  sorry

theorem phiDerivReal_integrableOn_section {k : ℤ} (hk : 0 ≤ k): IntegrableOn (phiDerivReal K L) (Set.Ioc (k : ℝ) (k + 1 : ℝ)) μ := by
  apply IntegrableOn.congr_fun_ae (f := fun x => (Nat.card G(L/K)_[⌈k + 1⌉] : ℝ) / (Nat.card G(L/K)_[0] : ℝ))
  apply integrableOn_const.2
  right
  dsimp [μ]
  exact measure_Ioc_lt_top
  unfold phiDerivReal EventuallyEq
  apply (ae_restrict_iff_subtype _).2
  apply ae_of_all
  intro ⟨a, ha⟩
  have ha' : ⌈a⌉ = k + 1 := by
    apply Int.ceil_eq_on_Ioc (k + 1) a ?_
    simp only [Int.cast_add, Int.cast_one, add_sub_cancel_right, ha]
  dsimp
  rw [max_eq_right]
  rw [ha']
  rw [ha']
  apply le_trans hk (by linarith)
  exact measurableSet_Ioc


theorem phiReal_eq_sum_card {u : ℝ} (hu : 0 ≤ u) : phiReal K L u = (1 / Nat.card G(L/K)_[0]) * ((∑ x in Finset.Icc 1 (⌈u⌉ - 1), Nat.card G(L/K)_[x]) + (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈u⌉])) := by
  unfold phiReal
  by_cases hu' : u = 0
  · simp only [hu', integral_same, one_div, Int.ceil_zero, zero_sub, Int.reduceNeg, neg_lt_self_iff, zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, CharP.cast_eq_zero, Left.neg_nonpos_iff, zero_le_one, max_eq_left, Int.cast_zero, sub_self, zero_mul, add_zero, mul_zero]
  · calc
      _ = ∫ (x : ℝ) in (0 : ℝ)..(⌈u⌉ - 1 : ℝ), phiDerivReal K L x ∂μ + ∫ (x : ℝ) in (⌈u⌉ - 1 : ℝ)..(u : ℝ), phiDerivReal K L x ∂μ := by
        have h : Set.Ioc 0 u = Set.Ioc 0 (⌈u⌉ - 1 : ℝ) ∪ (Set.Ioc (⌈u⌉ - 1 : ℝ) u) := by
          refine Eq.symm (Set.Ioc_union_Ioc_eq_Ioc ?h₁ ?h₂)
          rw [sub_nonneg, ← (Int.cast_one (R := ℝ)), Int.cast_le]
          apply Int.one_le_ceil_iff.2
          apply lt_of_le_of_ne hu
          exact fun a ↦ hu' (id (Eq.symm a))
          rw [sub_le_iff_le_add]
          apply le_of_lt (Int.ceil_lt_add_one u)
        rw [integral_of_le, integral_of_le, integral_of_le, h, MeasureTheory.setIntegral_union]
        · exact Set.Ioc_disjoint_Ioc_same
        · exact measurableSet_Ioc
        · have hbu : Set.Ioc 0 (⌈u⌉ - 1 : ℝ) = ⋃ (i ∈ Set.Icc 0 (⌈u⌉ - 1 - 1)), Set.Ioc (i : ℝ) (i + 1 : ℝ) := by
            ext x
            constructor
            <;> intro hx
            · apply Set.mem_iUnion.2
              use ⌈x⌉ - 1
              simp only [Set.mem_Icc, sub_nonneg, tsub_le_iff_right, sub_add_cancel, Int.cast_le,
                Set.mem_iUnion, Set.mem_Ioc, exists_and_left, exists_prop]
              constructor
              · rw [Int.cast_sub, Int.cast_one]
                linarith [Int.ceil_lt_add_one x]
              · constructor
                · constructor
                  · apply Int.one_le_ceil_iff.2 (Set.mem_Ioc.1 hx).1
                  · apply Int.ceil_le.2
                    rw [Int.cast_sub, Int.cast_one]
                    exact (Set.mem_Ioc.1 hx).2
                · rw [Int.cast_sub, Int.cast_one, sub_add_cancel]
                  exact Int.le_ceil x
            · simp only [Set.mem_Ioc]
              simp only [Set.mem_Icc, Set.mem_iUnion, Set.mem_Ioc, exists_and_left, exists_prop] at hx
              obtain ⟨i, hi1, hi2, hi3⟩ := hx
              constructor
              · apply lt_of_le_of_lt ?_ hi1
                simp only [Int.cast_nonneg, hi2.1]
              · apply le_trans hi3
                rw [← Int.cast_one (R := ℝ), ← Int.cast_add, ← Int.cast_sub, Int.cast_le]
                linarith [hi2.2]
          rw [hbu]
          apply (integrableOn_finite_biUnion _).2
          intro i hi
          apply phiDerivReal_integrableOn_section K L (Set.mem_Icc.1 hi).1
          exact Set.finite_Icc 0 (⌈u⌉ - 1 - 1)
        · apply IntegrableOn.mono_set (t := Set.Ioc (↑(⌈u⌉ - 1) : ℝ) (↑(⌈u⌉ - 1 : ℝ) + 1))
          nth_rw 1 [← Int.cast_one (R := ℝ)]
          rw [← Int.cast_sub]
          apply phiDerivReal_integrableOn_section K L (k := ⌈u⌉ - 1)
          apply sub_nonneg.2 (Int.one_le_ceil_iff.2 (lt_of_le_of_ne hu ?_))
          exact fun a ↦ hu' (id (Eq.symm a))
          apply Set.Ioc_subset_Ioc
          simp only [Int.cast_sub, Int.cast_one, le_refl]
          simp only [sub_add_cancel]
          apply Int.le_ceil u
        · linarith [Int.ceil_lt_add_one u]
        · rw [sub_nonneg, ← (Int.cast_one (R := ℝ)), Int.cast_le]
          apply Int.one_le_ceil_iff.2
          apply lt_of_le_of_ne hu
          exact fun a ↦ hu' (id (Eq.symm a))
        · exact hu
      _ = ∑ k in Finset.range (⌈u⌉ - 1).toNat, ∫ (x : ℝ) in ((Nat.cast : ℕ → ℝ) k : ℝ)..((Nat.cast : ℕ → ℝ) (k + 1) : ℝ), phiDerivReal K L x ∂μ +  ∫ (x : ℝ) in (⌈u⌉ - 1 : ℝ)..(u : ℝ), phiDerivReal K L x ∂μ := by
        rw [intervalIntegral.sum_integral_adjacent_intervals]
        congr
        rw [Nat.cast_zero]
        norm_cast
        rw [Int.toNat_of_nonneg]
        rw [sub_nonneg]
        apply Int.one_le_ceil_iff.2
        apply lt_of_le_of_ne hu
        exact fun a ↦ hu' (id (Eq.symm a))
        intro k _
        dsimp [IntervalIntegrable]
        constructor
        · rw [← Int.cast_natCast, ← Int.cast_natCast (k + 1), Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_one]
          apply phiDerivReal_integrableOn_section K L (k := (k : ℤ))
          exact Int.ofNat_zero_le k
        · simp only [Nat.cast_add, Nat.cast_one, add_lt_iff_neg_left, not_lt, zero_le_one, Set.Ioc_eq_empty, integrableOn_empty]
      _ = _ := by
        have h : ∑ k in Finset.range (⌈u⌉ - 1).toNat, ∫ x in (k : ℝ)..(↑(k + 1) : ℝ), phiDerivReal K L x ∂μ = ∑ k in Finset.Icc 1 (⌈u⌉ - 1), (Nat.card G(L/K)_[k] : ℝ) / (Nat.card G(L/K)_[0] : ℝ) := by
          rw [Finset.sum, Finset.sum]
          let i : ℕ → ℤ := fun x => x + 1
          let j : ℤ → ℕ := fun x => (x - 1).toNat
          apply Finset.sum_nbij' i j
          intro a ha
          dsimp [i]
          rw [Finset.mem_range] at ha
          apply Finset.mem_Icc.2
          constructor
          · refine Int.le_add_of_nonneg_left ?hi.left.h
            exact Int.ofNat_zero_le a
          · apply Int.le_sub_one_of_lt
            rw [← Nat.cast_lt (α := ℤ), Int.toNat_of_nonneg] at ha
            linarith [ha]
            rw [sub_nonneg]
            apply Int.one_le_ceil_iff.2
            apply lt_of_le_of_ne hu
            exact fun a ↦ hu' (id (Eq.symm a))
          intro a ha
          by_cases hu'' : ⌈u⌉ = 1
          · simp only [hu'', sub_self, zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.not_mem_empty] at ha
          · dsimp [j]
            rw [Finset.mem_Icc] at ha
            apply Finset.mem_range.2
            apply (Int.toNat_lt_toNat _).2
            linarith [ha.2]
            apply lt_of_le_of_ne
            rw [sub_nonneg]
            apply Int.one_le_ceil_iff.2
            apply lt_of_le_of_ne hu
            exact fun a ↦ hu' (id (Eq.symm a))
            exact Ne.symm (sub_ne_zero_of_ne hu'')
          intro a ha
          dsimp [i, j]
          simp only [add_sub_cancel_right, Int.toNat_ofNat]
          intro a ha
          dsimp [i, j]
          rw [Int.toNat_of_nonneg]
          ring
          rw [Finset.mem_Icc] at ha
          linarith [ha.1]
          intro a ha
          rw [integral_of_le, setIntegral_congr_fun (g := fun x => (Nat.card G(L/K)_[(i a)] : ℝ) / (Nat.card G(L/K)_[0] : ℝ))]
          simp only [Nat.cast_add, Nat.cast_one, MeasureTheory.integral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, smul_eq_mul, μ, Real.volume_Ioc, add_sub_cancel_left, ENNReal.ofReal_one, ENNReal.one_toReal,one_mul]
          exact measurableSet_Ioc
          simp only [Set.EqOn, phiDerivReal, i]
          intro x hx
          rw [max_eq_right, Int.ceil_eq_iff.2 ⟨by simp only [Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_natCast, Int.cast_one, add_sub_cancel_right, (Set.mem_Ioc.1 hx).1], (Set.mem_Ioc.1 hx).2⟩, Nat.cast_add, Nat.cast_one]
          apply Int.ceil_nonneg (le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg' a) (Set.mem_Ioc.1 hx).1))
          rw [Nat.cast_le]
          linarith
        rw [h, mul_add]
        congr
        · let e : ℤ ≃ ℤ := {
          toFun := fun x => x
          invFun := fun x => x
          left_inv := fun x => rfl
          right_inv := fun x => rfl
        }
          rw [Nat.cast_sum, Finset.mul_sum (Finset.Icc 1 (⌈u⌉ - 1)) (fun x => (Nat.card G(L/K)_[x] : ℝ)) (1 / (Nat.card G(L/K)_[0] : ℝ)), Finset.sum_equiv e]
          · dsimp [e]
            simp only [Finset.mem_Icc, implies_true]
          · intro i hi
            dsimp [e]
            rw [one_div, inv_mul_eq_div]
        · have h : ∫ (x : ℝ) in (⌈u⌉ - 1 : ℝ)..u, phiDerivReal K L x ∂μ = ∫ (x : ℝ) in (⌈u⌉ - 1 : ℝ)..u, (Nat.card G(L/K)_[⌈u⌉] : ℝ) / (Nat.card G(L/K)_[0] : ℝ) := by
            rw [integral_of_le, integral_of_le, μ]
            apply setIntegral_congr_fun
            exact measurableSet_Ioc
            simp only [Set.EqOn, phiDerivReal]
            intro x hx
            rw [max_eq_right, Int.ceil_eq_iff.2 ⟨(Set.mem_Ioc.1 hx).1, le_trans (Set.mem_Ioc.1 hx).2 (Int.le_ceil u)⟩]
            rw [← Int.cast_le (R := ℝ), Int.cast_zero]
            apply le_trans ?_ (Int.le_ceil x)
            apply le_of_lt (lt_of_le_of_lt ?_ (Set.mem_Ioc.1 hx).1)
            rw [sub_nonneg, ← Int.cast_one (R := ℝ)]
            apply Int.cast_le.2 (Int.one_le_ceil_iff.2 (lt_of_le_of_ne hu ?_))
            exact fun a ↦ hu' (id (Eq.symm a))
            apply le_of_lt
            linarith [Int.ceil_lt_add_one u]
            apply le_of_lt
            linarith [Int.ceil_lt_add_one u]
          simp only [h, intervalIntegral.integral_const, smul_eq_mul, Int.cast_max]
          rw [max_eq_right, Int.cast_sub, Int.cast_one]
          ring
          apply Int.cast_le.2 (sub_nonneg.2 (Int.one_le_ceil_iff.2 (lt_of_le_of_ne hu ?_)))
          exact fun a ↦ hu' (id (Eq.symm a))

theorem phiReal_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < phiReal K L x := by
  rw [phiReal_eq_sum_card K L (le_of_lt hx)]
  apply mul_pos
  · simp only [one_div, inv_pos, Nat.cast_pos, Nat.card_pos]
  · apply add_pos_of_nonneg_of_pos
    · apply Nat.cast_nonneg
    · apply mul_pos
      · rw [max_eq_right, Int.cast_sub, Int.cast_one, ← sub_add, sub_add_eq_add_sub]
        linarith [Int.ceil_lt_add_one x]
        apply Int.le_of_sub_one_lt
        simp only [zero_sub, Int.reduceNeg, neg_lt_sub_iff_lt_add, lt_add_iff_pos_right,
          Int.ceil_pos]
        exact hx
      · simp only [Nat.cast_pos, Nat.card_pos]

variable [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable K L] in
theorem phiReal_eq_phi {u : ℚ} (hu : 0 ≤ u) : phiReal K L u = phi K L u := by
  by_cases hu' : u = 0
  · simp only [hu', phi_zero_eq_zero, Rat.cast_zero, phiReal_zero_eq_zero]
  · rw [phiReal_eq_sum_card K L, phi_eq_sum_card]
    simp only [one_div, Rat.ceil_cast, Nat.cast_sum, Int.cast_max, Int.cast_zero, Int.cast_sub, Int.cast_one, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, Rat.cast_add, Rat.cast_sum, Rat.cast_sub, Rat.cast_max, Rat.cast_zero, Rat.cast_intCast, Rat.cast_one]
    apply lt_of_le_of_ne hu
    exact fun a ↦ hu' (id (Eq.symm a))
    exact Rat.cast_nonneg.mpr hu

theorem phiReal_eq_self_of_le_zero {u : ℝ} (hu : u ≤ 0) : phiReal K L u = u := by
  unfold phiReal phiDerivReal
  have h1 : u = ∫ (x : ℝ) in (0 : ℝ)..u, 1 ∂μ :=by
    rw [integral_of_ge hu]
    simp only [MeasureTheory.integral_const, MeasurableSet.univ, MeasureTheory.Measure.restrict_apply, Set.univ_inter, smul_eq_mul, mul_one]
    unfold μ
    rw [Real.volume_Ioc, ENNReal.toReal_ofReal]
    ring
    linarith [hu]
  nth_rw 2 [h1]
  apply integral_congr
  dsimp [Set.EqOn]
  intro x hx
  simp only [hu, Set.uIcc_of_ge, Set.mem_Icc] at hx
  rw [max_eq_left, div_self]
  apply ne_of_gt
  simp only [Nat.cast_pos, Nat.card_pos]
  apply Int.ceil_le.2 (by simp only [Int.cast_zero, hx.2])

set_option maxHeartbeats 0

theorem phiReal_sub_phiReal_le {u v : ℝ} (h : u ≤ v) (h' : 0 < u) : phiReal K L v - phiReal K L u ≤ (v - u) * phiDerivReal K L u := by
  by_cases hc : u = v
  · simp only [hc, sub_self, zero_mul]
    linarith
  · by_cases hceil : ⌈v⌉ = 1
    · have hceil' : ⌈u⌉ = 1 := by
        apply Int.ceil_eq_iff.mpr
        refine ⟨by simp only [Int.cast_one, sub_self, h'], le_trans h ?_⟩
        rw [← hceil]
        exact Int.le_ceil v
      rw [phiReal_eq_sum_card K L (le_of_lt h'), phiReal_eq_sum_card, phiDerivReal, ← mul_sub, one_div_mul_eq_div, ← mul_div_assoc, div_le_div_right, ← sub_sub, add_sub_right_comm, add_sub_assoc, hceil, hceil', sub_self]
      simp only [sub_self, max_self, Int.cast_zero, sub_zero, zero_add, zero_le_one, max_eq_right, tsub_le_iff_right]
      ring_nf
      linarith
      simp only [Nat.cast_pos, Nat.card_pos]
      exact le_of_lt (lt_of_lt_of_le h' h)
    · by_cases hu : ⌈u⌉ = 1
      · rw [phiReal_eq_sum_card K L (le_of_lt h'), phiReal_eq_sum_card, phiDerivReal, ← mul_sub, one_div_mul_eq_div, ← mul_div_assoc, div_le_div_right, ← sub_sub, add_sub_right_comm, add_sub_assoc, hu, sub_self]
        simp only [zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, max_self, Nat.cast_sum, CharP.cast_eq_zero, sub_zero, Int.cast_max, Int.cast_zero, Int.cast_sub, Int.cast_one, zero_le_one, max_eq_right]
        rw [max_eq_right]
        calc
          _ ≤ ∑ x ∈ Finset.Icc 1 (⌈v⌉ - 1), (Nat.card ↥ G(L/K)_[1]) + ((v - (⌈v⌉ - 1)) * (Nat.card G(L/K)_[⌈v⌉]) - u * (Nat.card G(L/K)_[1])) := by
            simp only [add_le_add_iff_right, ← Nat.cast_sum, Nat.cast_le]
            apply Finset.sum_le_sum
            intro i hi
            apply Nat.card_mono
            exact Set.toFinite (G(L/K)_[1] : Set (L ≃ₐ[K] L))
            apply lowerRamificationGroup.antitone
            apply (Finset.mem_Icc.1 hi).1
          _ ≤ (⌈v⌉ - 1) * (Nat.card G(L/K)_[1]) + ((v - (⌈v⌉ - 1)) * (Nat.card G(L/K)_[⌈v⌉]) - u * (Nat.card G(L/K)_[1])) := by
            simp only [Finset.sum_const, Int.card_Icc, sub_add_cancel, Int.pred_toNat, smul_eq_mul, Nat.cast_mul, add_le_add_iff_right, Nat.cast_pos, Nat.card_pos, mul_le_mul_right]
            rw [Nat.cast_sub, Nat.cast_one, sub_le_sub_iff_right, ← Int.cast_natCast, Int.toNat_of_nonneg]
            apply Int.ceil_nonneg
            apply le_trans (le_of_lt h') h
            rw [← Nat.cast_le (α := ℤ), Int.toNat_of_nonneg, Nat.cast_one]
            apply Int.one_le_ceil_iff.mpr
            apply lt_of_lt_of_le h' h
            apply Int.ceil_nonneg
            apply le_trans (le_of_lt h') h
          _ ≤ (⌈v⌉ - 1) * (Nat.card G(L/K)_[1]) + ((v - (⌈v⌉ - 1)) * (Nat.card G(L/K)_[1]) - u * (Nat.card G(L/K)_[1])) := by
            simp only [add_le_add_iff_left, tsub_le_iff_right, sub_add_cancel]
            rw [mul_le_mul_left, Nat.cast_le]
            apply Nat.card_mono
            exact Set.toFinite (G(L/K)_[1] : Set (L ≃ₐ[K] L))
            apply lowerRamificationGroup.antitone
            apply Int.one_le_ceil_iff.mpr
            apply lt_of_lt_of_le h' h
            linarith [Int.ceil_lt_add_one v]
          _ ≤ _ := by
            ring
            simp only [le_refl]
        rw [sub_nonneg, ← Int.cast_one, Int.cast_le]
        apply Int.one_le_ceil_iff.mpr
        apply lt_of_lt_of_le h' h
        rw [← Nat.cast_zero, Nat.cast_lt]
        apply Ramification_Group_card_pos K L (u := 0)
        apply le_of_lt (lt_of_lt_of_le h' h)
      · have h1 : Finset.Icc 1 (⌈v⌉ - 1) = Finset.Icc 1 (⌈u⌉ - 1) ∪ Finset.Icc ⌈u⌉ (⌈v⌉ - 1) := by
          nth_rw 2 [← sub_add_cancel ⌈u⌉ 1]
          rw [Finset.Icc_union_Icc_eq_Icc (a := 1) (b := (⌈u⌉ - 1)) (c := (⌈v⌉ - 1))]
          apply Int.le_of_sub_one_lt
          simp only [sub_self, sub_pos]
          apply lt_of_le_of_ne
          apply Int.one_le_ceil_iff.mpr h'
          exact fun a ↦ hu (id (Eq.symm a))
          simp only [tsub_le_iff_right, sub_add_cancel]
          exact Int.ceil_le_ceil h
        rw [phiReal_eq_sum_card K L (le_of_lt h'), phiReal_eq_sum_card, phiDerivReal, ← mul_sub, one_div_mul_eq_div, ← mul_div_assoc, div_le_div_right, ← sub_sub, add_sub_right_comm, add_sub_assoc, h1, Finset.sum_union, Nat.cast_add, add_sub_cancel_left, max_eq_right, max_eq_right]
        calc
          _ ≤ ∑ x ∈ Finset.Icc ⌈u⌉ (⌈v⌉ - 1), Nat.card G(L/K)_[⌈u⌉] + ((v - (⌈v⌉ - 1)) * (Nat.card G(L/K)_[⌈v⌉] ) - (u - (⌈u⌉ - 1)) * (Nat.card G(L/K)_[⌈u⌉])) := by
            simp only [Int.cast_sub, Int.cast_one, add_le_add_iff_right, Nat.cast_le]
            apply Finset.sum_le_sum
            intro i hi
            apply Nat.card_mono
            exact Set.toFinite (G(L/K)_[⌈u⌉] : Set (L ≃ₐ[K] L))
            apply lowerRamificationGroup.antitone K L (Finset.mem_Icc.1 hi).1
          _ ≤ ∑ x ∈ Finset.Icc ⌈u⌉ (⌈v⌉ - 1), Nat.card G(L/K)_[⌈u⌉] + ((v - (⌈v⌉ - 1)) * (Nat.card ↥ G(L/K)_[⌈u⌉] ) - (u - (⌈u⌉ - 1)) * (Nat.card G(L/K)_[⌈u⌉])) := by
            simp only [add_le_add_iff_left, sub_eq_add_neg (b := (u - (↑⌈u⌉ - 1)) * ↑(Nat.card ↥ G(L/K)_[⌈u⌉] )), add_le_add_iff_right]
            rw [mul_le_mul_left, Nat.cast_le]
            apply Nat.card_mono
            exact Set.toFinite (G(L/K)_[⌈u⌉] : Set (L ≃ₐ[K] L))
            apply lowerRamificationGroup.antitone K L
            exact Int.ceil_le_ceil h
            rw [sub_pos, sub_lt_iff_lt_add]
            exact Int.ceil_lt_add_one v
          _ ≤ _ := by
            simp only [Finset.sum_const, Int.card_Icc, sub_add_cancel, smul_eq_mul, Nat.cast_mul]
            rw [← Int.cast_natCast, Int.toNat_of_nonneg, ← sub_mul, ← add_mul, Int.cast_sub]
            have h1 : (↑⌈v⌉ - ↑⌈u⌉ + (v - (↑⌈v⌉ - 1) - (u - (↑⌈u⌉ - 1)))) = v - u := by ring
            rw [h1, mul_le_mul_left, max_eq_right]
            apply Int.ceil_nonneg (le_of_lt h')
            linarith [lt_of_le_of_ne h hc]
            apply sub_nonneg.2 (Int.ceil_le_ceil h)
        simp only [sub_nonneg, Int.one_le_ceil_iff.2 h']
        simp only [sub_nonneg, Int.one_le_ceil_iff.2 (lt_of_lt_of_le h' h)]
        apply Disjoint.symm ((fun {α} {s t} ↦ Finset.disjoint_left.mpr) ?_)
        intro a ha
        simp only [Finset.mem_Icc] at *
        push_neg
        intro ha'
        apply lt_of_lt_of_le (by linarith) ha.1
        simp only [Nat.cast_pos, Nat.card_pos]
        exact le_of_lt (lt_of_lt_of_le h' h)


theorem le_phiReal_sub_phiReal {u v : ℝ} (h : u ≤ v) (hu : 0 < u) : (v - u) * phiDerivReal K L v ≤ phiReal K L v - phiReal K L u := by
  rw [phiReal_eq_sum_card, phiReal_eq_sum_card, phiDerivReal, ← one_div_mul_eq_div, mul_comm, ← mul_sub, mul_assoc, mul_le_mul_left, max_eq_right, max_eq_right, max_eq_right]
  calc
    _ ≤ (∑ x ∈ Finset.Icc 1 (⌈v⌉ - 1), Nat.card G(L/K)_[⌈v⌉]) + (v - (⌈v⌉ - 1)) * (Nat.card G(L/K)_[⌈v⌉]) - ((∑ x ∈ Finset.Icc 1 (⌈u⌉ - 1), Nat.card G(L/K)_[⌈v⌉]) + (u - (⌈u⌉ - 1)) * (Nat.card G(L/K)_[⌈v⌉] )) := by
      simp only [Finset.sum_const, Int.card_Icc, sub_add_cancel, Int.pred_toNat, smul_eq_mul, Nat.cast_mul]
      rw [Nat.cast_sub, Nat.cast_sub, ← (Int.cast_natCast (n := ⌈v⌉.toNat)), Int.toNat_of_nonneg, ← (Int.cast_natCast (n := ⌈u⌉.toNat)), Int.toNat_of_nonneg]
      simp only [Nat.cast_one]
      ring
      simp only [le_refl]
      apply Int.ceil_nonneg (le_of_lt hu)
      apply Int.ceil_nonneg (le_of_lt (lt_of_lt_of_le hu h))
      apply (Int.le_toNat (Int.ceil_nonneg (le_of_lt hu))).mpr ?_
      simp only [Nat.cast_one]
      exact Int.one_le_ceil_iff.mpr hu
      apply (Int.le_toNat ?_).mpr ?_
      apply Int.ceil_nonneg (le_of_lt (lt_of_lt_of_le hu h))
      simp only [Nat.cast_one]
      apply Int.one_le_ceil_iff.mpr (lt_of_lt_of_le hu h)
    _ ≤ (∑ x ∈ Finset.Icc 1 (⌈v⌉ - 1), Nat.card G(L/K)_[⌈v⌉]) + (v - (⌈v⌉ - 1)) * (Nat.card G(L/K)_[⌈v⌉]) - ((∑ x ∈ Finset.Icc 1 ⌈u⌉, Nat.card G(L/K)_[⌈v⌉]) - (⌈u⌉ - u) * (Nat.card ↥ G(L/K)_[⌈v⌉])) := by
      apply (sub_le_sub_iff_left (a := (∑ x ∈ Finset.Icc 1 (⌈v⌉ - 1), Nat.card G(L/K)_[⌈v⌉]) + (v - (⌈v⌉ - 1)) * (Nat.card G(L/K)_[⌈v⌉]))).2
      rw [insert_Icc_right, Finset.sum_insert, add_comm,Nat.cast_add, add_sub_assoc]
      nth_rw 2 [← (one_mul (Nat.card ↥ G(L/K)_[⌈v⌉]))]
      rw [Nat.cast_mul, ← sub_mul, ← sub_add, ← sub_add, Nat.cast_one, sub_add_comm]
      simp only [Finset.mem_Icc, Int.one_le_ceil_iff, le_sub_self_iff, Int.reduceLE, and_false, not_false_eq_true]
      exact Int.one_le_ceil_iff.mpr hu
    _ ≤ (∑ x ∈ Finset.Icc 1 (⌈v⌉ - 1), Nat.card G(L/K)_[x]) + (v - (⌈v⌉ - 1)) * (Nat.card G(L/K)_[⌈v⌉]) - ((∑ x ∈ Finset.Icc 1 ⌈u⌉, Nat.card G(L/K)_[x]) - (⌈u⌉ - u) * (Nat.card ↥ G(L/K)_[⌈v⌉])) := by
      rw [← sub_add]
      conv =>
        right
        rw [← sub_add]
      rw [add_le_add_iff_right, add_sub_right_comm, add_sub_right_comm, add_le_add_iff_right]
      by_cases huv : ⌈u⌉ = ⌈v⌉
      · rw [huv]
        nth_rw 2 [insert_Icc_right]
        nth_rw 4 [insert_Icc_right]
        rw [Finset.sum_insert, Nat.cast_add, ← sub_sub, sub_right_comm, sub_self]
        rw [Finset.sum_insert, Nat.cast_add, ← sub_sub, sub_right_comm, sub_self]
        simp only [Finset.mem_Icc, Int.one_le_ceil_iff, le_sub_self_iff, Int.reduceLE, and_false,not_false_eq_true]
        simp only [Finset.mem_Icc, Int.one_le_ceil_iff, le_sub_self_iff, Int.reduceLE, and_false,not_false_eq_true]
        repeat apply Int.one_le_ceil_iff.mpr (lt_of_lt_of_le hu h)
      · have h1 : Finset.Icc 1 (⌈v⌉ - 1) = Finset.Icc 1 ⌈u⌉ ∪ Finset.Ioc ⌈u⌉ (⌈v⌉ - 1) := by
          rw [← Set.toFinset_Icc, ← Set.toFinset_Icc, ← Set.toFinset_Ioc, ← Set.toFinset_union]
          apply Set.toFinset_congr
          symm
          apply Set.Icc_union_Ioc_eq_Icc
          exact Int.one_le_ceil_iff.mpr hu
          apply Int.le_sub_one_of_lt (lt_of_le_of_ne ?_ ?_)
          apply Int.ceil_le_ceil h
          exact huv
        have hd : Disjoint (Finset.Icc 1 ⌈u⌉) (Finset.Ioc ⌈u⌉ (⌈v⌉ - 1)) := by
          apply Finset.disjoint_left.mpr ?_
          intro a ha
          simp only [Finset.mem_Icc] at ha
          simp only [Finset.mem_Ioc]
          apply Decidable.not_and_iff_or_not.mpr ?_
          left
          push_neg
          exact ha.2
        rw [h1, Finset.sum_union hd, add_comm, Nat.cast_add, add_sub_assoc, sub_self, add_zero]
        rw [Finset.sum_union hd, add_comm, Nat.cast_add, add_sub_assoc, sub_self, add_zero, Nat.cast_le]
        apply Finset.sum_le_sum
        intro i hi
        apply Nat.card_mono
        exact Set.toFinite (G(L/K)_[i] : Set (L ≃ₐ[K] L))
        apply lowerRamificationGroup.antitone
        apply le_trans (Finset.mem_Ioc.1 hi).2 (by linarith)
    _ ≤ (∑ x ∈ Finset.Icc 1 (⌈v⌉ - 1), Nat.card G(L/K)_[x]) + (v - (⌈v⌉ - 1)) * (Nat.card G(L/K)_[⌈v⌉]) - ((∑ x ∈ Finset.Icc 1 ⌈u⌉, Nat.card G(L/K)_[x]) - (⌈u⌉ - u) * (Nat.card ↥ G(L/K)_[⌈u⌉])) := by
      by_cases hu' : u = ⌈u⌉
      · rw [sub_le_sub_iff_left, sub_le_sub_iff_left]
        nth_rw 2 [hu']
        nth_rw 4 [hu']
        rw [sub_self, zero_mul, zero_mul]
      · rw [sub_le_sub_iff_left, sub_le_sub_iff_left, mul_le_mul_left, Nat.cast_le]
        apply Nat.card_mono
        exact Set.toFinite (G(L/K)_[⌈u⌉] : Set (L ≃ₐ[K] L))
        apply lowerRamificationGroup.antitone
        exact Int.ceil_le_ceil h
        apply lt_of_le_of_ne
        linarith [Int.le_ceil u]
        exact Ne.symm (sub_ne_zero_of_ne fun a ↦ hu' (id (Eq.symm a)))
    _ ≤ _ := by
      rw [Int.cast_sub, Int.cast_one, (sub_le_sub_iff_left (↑(∑ x ∈ Finset.Icc 1 (⌈v⌉ - 1), Nat.card ↥ G(L/K)_[x] ) + (v - (↑⌈v⌉ - 1)) * ↑(Nat.card ↥ G(L/K)_[⌈v⌉])))]
      nth_rw 2 [insert_Icc_right]
      rw [Finset.sum_insert]
      nth_rw 2 [← (one_mul (Nat.card ↥ G(L/K)_[⌈u⌉]))]
      conv =>
        right
        rw [add_comm, Nat.cast_add, add_sub_assoc, Nat.cast_mul, Nat.cast_one, ← sub_mul, ← sub_add, sub_add_comm]
      rw [Int.cast_sub, Int.cast_one, ← sub_add, sub_add_comm]
      simp only [Finset.mem_Icc, Int.one_le_ceil_iff, le_sub_self_iff, Int.reduceLE, and_false, not_false_eq_true]
      exact Int.one_le_ceil_iff.mpr hu
  linarith [Int.one_le_ceil_iff.mpr hu]
  linarith [Int.one_le_ceil_iff.mpr (lt_of_lt_of_le hu h)]
  apply Int.ceil_nonneg (le_of_lt (lt_of_lt_of_le hu h))
  refine one_div_pos.mpr ?_
  rw [← Nat.cast_zero, Nat.cast_lt]
  apply Ramification_Group_card_pos K L (u := 0)
  apply le_of_lt hu
  apply le_of_lt (lt_of_lt_of_le hu h)

theorem phiReal_StrictMono : StrictMono (phiReal K L) := by
  intro a b hab
  by_cases hb : 0 < b
  · by_cases ha : 0 < a
    · apply lt_of_sub_pos
      apply lt_of_lt_of_le _ (le_phiReal_sub_phiReal K L (le_of_lt hab) ha)
      apply mul_pos (by linarith [hab]) (phiDerivReal_pos K L)
    · push_neg at ha
      rw [phiReal_eq_self_of_le_zero K L ha]
      apply lt_of_le_of_lt ha (phiReal_pos_of_pos K L hb)
  · push_neg at hb
    obtain ha' := lt_of_lt_of_le hab hb
    rw [phiReal_eq_self_of_le_zero K L (le_of_lt ha'), phiReal_eq_self_of_le_zero K L hb]
    exact hab

theorem phiReal_injective {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : Function.Injective (phiReal K L) := by
  intro a1 a2 h
  contrapose! h
  by_cases h1 : a1 > a2
  · apply ne_of_gt (phiReal_StrictMono K L h1)
  · push_neg at *
    apply ne_of_lt (phiReal_StrictMono K L (lt_of_le_of_ne h1 h))

variable [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable K L] in
theorem phiReal_phi_ceil_eq_aux {u : ℝ} (hu : 0 ≤ u) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : ∃ u' : ℚ, ⌈u⌉ = ⌈u'⌉ ∧ ⌈phiReal K L u⌉ = ⌈phi K L u'⌉ := by
  by_cases hc : u = ⌈u⌉
  · use ⌈u⌉
    constructor
    · exact Eq.symm (Int.ceil_intCast ⌈u⌉)
    · rw [hc, Int.ceil_intCast ⌈u⌉,← Rat.cast_intCast, phiReal_eq_phi K L (u := ⌈u⌉), Rat.ceil_cast]
      apply Int.cast_nonneg.mpr (Int.ceil_nonneg hu)
  · by_cases hc' : phiReal K L u = ⌈phiReal K L u⌉
    · have h : ∃ u' : ℚ, u' = u := by
        have h' : ∃ u' : ℚ, phi K L u' = ⌈phiReal K L u⌉ := by apply (phi_Bijective_aux K L hgen).2
        obtain ⟨u', hu'⟩ := h'
        use u'
        have haux : (phi K L u' : ℝ) = ⌈phiReal K L u⌉ := by simp only [hu', Rat.cast_intCast]
        rw [← hc', ← phiReal_eq_phi K L ?_] at haux
        apply phiReal_injective K L hgen haux
        have h : (0 : ℝ) ≤ phi K L u' := by
          rw [haux]
          apply phiReal_nonneg K L hu
        by_contra hc
        push_neg at hc
        have h' : phi K L u' < (0 : ℝ) := by
          rw [phi_eq_self_of_le_zero K L (le_of_lt hc)]
          exact Rat.cast_lt_zero.mpr hc
        absurd h
        push_neg
        exact h'
      obtain ⟨u', hu'⟩ := h
      use u'
      rw [← hu']
      constructor
      · exact Rat.ceil_cast u'
      · rw [phiReal_eq_phi K L, Rat.ceil_cast]
        rw [← Rat.cast_le (K := ℝ), Rat.cast_zero, hu']
        exact hu
    · have h' : ∃ u' : ℚ, u ≤ u' ∧ u' - u ≤ ⌈u⌉ - u ∧ u' - u ≤ ⌈phiReal K L u⌉ - phiReal K L u := by
        have h2 : ∃ u' : ℚ, (u' : ℝ) ∈ (Set.Ici u ∩ Set.Icc u ⌈u⌉ ∩ Set.Icc u (u + ⌈phiReal K L u⌉ - (phiReal K L u))) := by
          have hnem : (Set.Ioi u ∩ Set.Ioo u ↑⌈u⌉ ∩ Set.Ioo u (u + ↑⌈phiReal K L u⌉ - phiReal K L u)).Nonempty := by
            use u + ((1/(2 : ℝ)) * min (⌈u⌉ - u) (⌈phiReal K L u⌉ - (phiReal K L u)))
            have hu1 : u < u + ((1/(2 : ℝ)) * min (⌈u⌉ - u) (⌈phiReal K L u⌉ - (phiReal K L u))) := by
              simp only [one_div, lt_add_iff_pos_right, inv_pos, Nat.ofNat_pos, mul_pos_iff_of_pos_left, lt_min_iff, sub_pos]
              constructor
              · apply lt_of_le_of_ne (Int.le_ceil u) hc
              · apply lt_of_le_of_ne (Int.le_ceil (phiReal K L u)) hc'
            have hu2 : u + ((1/(2 : ℝ)) * min (⌈u⌉ - u) (⌈phiReal K L u⌉ - (phiReal K L u))) < ⌈u⌉ := by
              nth_rw 2 [← sub_add_cancel (⌈u⌉ : ℝ) u]
              rw [add_comm, add_lt_add_iff_right]
              calc
                _ < min (⌈u⌉ - u) (⌈phiReal K L u⌉ - (phiReal K L u)) := by
                  rw [one_div_mul_eq_div]
                  apply half_lt_self
                  simp only [lt_min_iff, sub_pos]
                  constructor
                  · apply lt_of_le_of_ne (Int.le_ceil u) hc
                  · apply lt_of_le_of_ne (Int.le_ceil (phiReal K L u)) hc'
                _ ≤ _ := by apply min_le_left
            have hu3 : u + ((1/(2 : ℝ)) * min (⌈u⌉ - u) (⌈phiReal K L u⌉ - (phiReal K L u))) < u + ↑⌈phiReal K L u⌉ - phiReal K L u := by
              rw [add_sub_assoc, add_lt_add_iff_left]
              calc
                _ < min (⌈u⌉ - u) (⌈phiReal K L u⌉ - (phiReal K L u)) := by
                  rw [one_div_mul_eq_div]
                  apply half_lt_self
                  simp only [lt_min_iff, sub_pos]
                  constructor
                  · apply lt_of_le_of_ne (Int.le_ceil u) hc
                  · apply lt_of_le_of_ne (Int.le_ceil (phiReal K L u)) hc'
                _ ≤ _ := by apply min_le_right
            constructor
            · constructor
              · rw [Set.mem_Ioi]
                apply hu1
              · rw [Set.mem_Ioo]
                refine ⟨hu1, hu2⟩
            · rw [Set.mem_Ioo]
              refine ⟨hu1, hu3⟩
          have h3' : ((Set.Ioi u ∩ Set.Ioo u ⌈u⌉ ∩ Set.Ioo u (u + ⌈phiReal K L u⌉ - (phiReal K L u))) ∩ (Set.range ((↑) : ℚ → ℝ) : Set ℝ)).Nonempty := by
            apply dense_iff_inter_open.1
            apply Rat.denseRange_cast
            apply IsOpen.inter (IsOpen.inter isOpen_Ioi isOpen_Ioo) isOpen_Ioo
            exact hnem
          have h3 : ((Set.Ici u ∩ Set.Icc u ⌈u⌉ ∩ Set.Icc u (u + ⌈phiReal K L u⌉ - (phiReal K L u))) ∩ (Set.range ((↑) : ℚ → ℝ) : Set ℝ)).Nonempty := by
            have hsub : ((Set.Ioi u ∩ Set.Ioo u ⌈u⌉ ∩ Set.Ioo u (u + ⌈phiReal K L u⌉ - (phiReal K L u))) ∩ (Set.range ((↑) : ℚ → ℝ) : Set ℝ)) ⊆ ((Set.Ici u ∩ Set.Icc u ⌈u⌉ ∩ Set.Icc u (u + ⌈phiReal K L u⌉ - (phiReal K L u))) ∩ (Set.range ((↑) : ℚ → ℝ) : Set ℝ)) := by
              intro x hx
              obtain ⟨⟨⟨hx1, hx2⟩, hx3⟩, hx4⟩ := hx
              refine ⟨⟨⟨Set.mem_Ici_of_Ioi hx1, le_of_lt (Set.mem_Ioo.1 hx2).1, le_of_lt (Set.mem_Ioo.1 hx2).2⟩, le_of_lt (Set.mem_Ioo.1 hx3).1, le_of_lt (Set.mem_Ioo.1 hx3).2⟩, hx4⟩
            apply Set.Nonempty.mono hsub h3'
          obtain ⟨u', ⟨⟨hu'1, hu'2⟩, hu'3⟩, hu'4⟩ := h3
          have h4 : (((↑) : ℚ → ℝ)⁻¹' {u'}).Nonempty := by
            exact hu'4
          obtain ⟨u'', hu''⟩ := h4
          use u''
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hu''
          rw [hu'']
          refine ⟨⟨hu'1, hu'2⟩, hu'3⟩
        obtain ⟨u', hu'⟩ := h2
        use u'
        obtain ⟨⟨hu'1, hu'2⟩ , hu'3⟩ := hu'
        constructor
        · exact hu'1
        · constructor
          · rw [sub_le_sub_iff_right]
            apply (Set.mem_Icc.1 hu'2).2
          · rw [← add_sub_cancel_right (⌈phiReal K L u⌉ - phiReal K L u) u, sub_le_sub_iff_right]
            linarith [(Set.mem_Icc.1 hu'3).2]
      obtain ⟨u', hu'1, hu'2, hu'3⟩ := h'
      use u'
      constructor
      · symm
        apply_mod_cast Int.ceil_eq_ceil hu'1 hu'2
      · rw [← Rat.ceil_cast (α := ℝ), ← phiReal_eq_phi K L (u := u')]
        have h : phiReal K L u' - phiReal K L u ≤ ⌈phiReal K L u⌉ - phiReal K L u := by
          apply le_trans (b := (u' - u) * phiDerivReal K L u)
          apply phiReal_sub_phiReal_le K L hu'1
          apply lt_of_le_of_ne hu
          by_contra hcon
          have hc' : u = ⌈u⌉ := by rw [← hcon, Int.ceil_zero, Int.cast_zero]
          absurd hc'
          exact hc
          apply le_trans (b := u' - u)
          nth_rw 2 [← mul_one (u' - u)]
          by_cases hc'' : 0 < u' - u
          · rw [mul_le_mul_left]
            unfold phiDerivReal
            apply (div_le_one _).2
            rw [Nat.cast_le]
            apply Nat.card_mono
            exact Set.toFinite (G(L/K)_[0] : Set (L ≃ₐ[K] L))
            apply lowerRamificationGroup.antitone
            exact Int.le_max_left 0 ⌈u⌉
            rw [← Nat.cast_zero, Nat.cast_lt]
            apply Ramification_Group_card_pos K L (u := 0)
            exact hc''
          · have h : u' - u = 0 := by
              apply Eq.symm (eq_of_le_of_not_lt (by linarith [hu'1]) hc'')
            rw [h, zero_mul, zero_mul]
          exact hu'3
        apply_mod_cast Eq.symm (Int.ceil_eq_ceil _ h)
        apply (phiReal_StrictMono K L).monotone hu'1
        apply Rat.cast_nonneg.1 (le_trans hu hu'1)

variable [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable K L] [Algebra.IsSeparable K K'] [Algebra.IsSeparable K' L] [CompleteSpace K'] [CompleteSpace K] [Normal K' L] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[K'])] [Algebra.IsSeparable ↥𝒪[K'] ↥𝒪[L]] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])] in
theorem herbrand_Real (u : ℝ) (hu : 0 ≤ u) {gen : 𝒪[K']} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) {gen' : 𝒪[L]} (hgen' : Algebra.adjoin 𝒪[K] {gen'} = ⊤) {gen'' : 𝒪[L]} (hgen'' : Algebra.adjoin 𝒪[K'] {gen''} = ⊤) : G(L/K)_[⌈u⌉].map (AlgEquiv.restrictNormalHom K') = G(K'/K)_[⌈phiReal K' L u⌉] := by
  obtain ⟨u', hu'1, hu'2⟩ := phiReal_phi_ceil_eq_aux K' L (u := u) hu hgen''
  rw [hu'1, hu'2]
  apply herbrand (K := K) (K' := K') (L := L) u' hgen hgen'

variable [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable K L] [Algebra.IsSeparable K K'] [Algebra.IsSeparable K' L] [CompleteSpace K'] [CompleteSpace K] [Normal K' L] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[K'])] [Algebra.IsSeparable ↥𝒪[K'] ↥𝒪[L]] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])] in
theorem phiDerivReal_comp {u : ℝ} (hu : 0 ≤ u) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) {gen' : 𝒪[L]} (hgen' : Algebra.adjoin 𝒪[K'] {gen'} = ⊤) {gen'' : 𝒪[K']} (hgen'' : Algebra.adjoin 𝒪[K] {gen''} = ⊤) {gen''' : 𝒪[L]} (hgen''' : Algebra.adjoin 𝒪[K] {gen'''} = ⊤) : (phiDerivReal K' L u) * phiDerivReal K K' (phiReal K' L u) = phiDerivReal K L u := by
  unfold phiDerivReal
  rw [← mul_div_mul_comm]
  congr
  · rw [← Int.ceil_intCast (α := ℝ) (z := (max 0 ⌈u⌉)), ← RamificationGroup_card_comp_aux K K' L ?_ hgen hgen', mul_comm]
    congr 1
    rw [max_eq_right, ← herbrand_Real K K' L _ hu hgen'' hgen''' hgen', max_eq_right]
    simp only [Subgroup.mem_map, Int.ceil_intCast]
    apply Int.ceil_nonneg hu
    apply Int.ceil_nonneg
    apply phiReal_nonneg K' L hu
    simp only [Int.cast_max, Int.cast_zero, le_max_iff, le_refl, Int.cast_nonneg, true_or]
  · rw [← Int.ceil_zero (α := ℝ), ← RamificationGroup_card_comp_aux K K' L (by linarith) hgen hgen', mul_comm]
    congr 1
    rw [herbrand_Real K K' L _ (by linarith) hgen'' hgen''' hgen', phiReal_zero_eq_zero]
