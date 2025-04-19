import RamificationGroup.UpperNumbering

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open QuotientGroup IntermediateField DiscreteValuation Valued Valuation HerbrandFunction

--variable (μ : MeasureTheory.Measure ℝ)
variable (K K' L : Type*) {ΓK : outParam Type*} [Field K] [Field K'] [Field L] [vK : Valued K ℤₘ₀] [vK' : Valued K' ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK.v] [IsDiscrete vK'.v] [IsDiscrete vL.v] [Algebra K L] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L] [IsValExtension vK.v vK'.v] [IsValExtension vK'.v vL.v] [IsValExtension vK.v vL.v] [Normal K K'] [Normal K L] [FiniteDimensional K L] [FiniteDimensional K K'] [FiniteDimensional K' L]


noncomputable def μ : MeasureTheory.Measure ℝ := MeasureTheory.volume

noncomputable def phiDerivReal (u : ℝ) : ℝ :=
  (Nat.card G(L/K)_[(max 0 ⌈u⌉)] : ℝ) / (Nat.card G(L/K)_[0] : ℝ)

noncomputable def phiReal (u : Real) : Real := ∫ x in (0 : ℝ)..u, phiDerivReal K L x ∂μ

--theorem continuous_phiDerivReal_aux : Continuous (phiDerivReal (K := K) (L := L)) := by sorry
open MeasureTheory.MeasureSpace intervalIntegral

--theorem phiReal_eq_phi {u : ℚ} : phiReal K L u = phi K L u := by sorry


theorem phiReal_zero_eq_zero : phiReal K L 0 = 0 := by
  unfold phiReal
  simp only [intervalIntegral.integral_same]


theorem phiReal_one_le_one : phiReal K L 1 ≤ 1 := by
  unfold phiReal
  rw [integral_of_le, MeasureTheory.setIntegral_congr_fun (g := fun x => phiDerivReal K L 1) measurableSet_Ioc, MeasureTheory.setIntegral_const]
  -- rw [integral_congr (g := fun x => phiDerivReal K L 1), integral_const' (phiDerivReal K L 1)]
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

theorem phiReal_nonneg {u : ℝ} (h : 0 ≤ u) : 0 ≤ phiReal K L u := by
  simp only [phiReal, integral_of_le h]
  apply MeasureTheory.setIntegral_nonneg_ae measurableSet_Ioc
  unfold Filter.Eventually phiDerivReal
  apply MeasureTheory.ae_of_all
  intro a _
  apply div_nonneg
  apply Nat.cast_nonneg
  apply Nat.cast_nonneg

#check intervalIntegral.differentiableOn_integral_of_continuous

-- theorem phiReal_hasFDeriv {x : ℝ} :HasFDerivAt (𝕜 := ℝ) (phiReal K L) (ContinuousLinearMap.smulRight (S := ℝ) 1 (phiDerivReal K L x)) x:= by
--   apply hasFDerivAt_iff_hasDerivAt.2
--   sorry

-- theorem phiReal_hasDeriv {x : ℝ} : HasDerivAt (phiReal K L) (phiDerivReal K L x) x := by
--   apply hasDerivAt_iff_hasFDerivAt.2
--   apply phiReal_hasFDeriv

-- theorem phiReal_Defferentiable : Differentiable ℝ (phiReal K L) := by
--   dsimp [Differentiable, DifferentiableAt]
--   intro x
--   use (ContinuousLinearMap.smulRight (S := ℝ) 1 (phiDerivReal K L x))
--   apply phiReal_hasFDeriv


-- theorem aux_2 : ↑(Nat.card ↥ G(K'/K)_[⌈(Nat.card ↥ G(L/K')_[1] : ℝ) / ↑(Nat.card ↥ G(L/K')_[0] : ℝ)⌉] ) / ↑(Nat.card ↥ G(K'/K)_[0] : ℝ) =
--   ↑(Nat.card ↥ G(L/K)_[1] : ℝ) / ↑(Nat.card ↥ G(L/K)_[0] : ℝ) := by
--       calc
--       _ = (Nat.card G(K'/K)_[⌈phi K' L 1⌉] : ℝ) / (Nat.card G(K'/K)_[0] : ℝ) := by
--         sorry
--       _ = (Nat.card (G(L/K)_[⌈(1 : ℚ)⌉].map (AlgEquiv.restrictNormalHom K'))) / (Nat.card G(K'/K)_[0] : ℝ) := by
--         sorry
--       _ = (Nat.card G(L/K)_[1] : ℝ) / (Nat.card G(L/K)_[0] : ℝ) := by
--         sorry

set_option maxHeartbeats 0

open Pointwise

#check Subgroup.card_mul_index
#check Subgroup.index_eq_card

#check AlgHom.restrictScalars
#check QuotientGroup.quotientInfEquivProdNormalQuotient

--for lower
instance {u : ℤ} : Subgroup.Normal (lowerRamificationGroup K L u) := sorry

#check Subgroup.map_comap_eq
#check Subgroup.map_comap_eq_self_of_surjective
#check QuotientGroup.quotientKerEquivOfSurjective


noncomputable def Subgroup_map {G H : Type*} [Group G] [Group H] {N : Subgroup G} {f : G →* H} (h : Function.Surjective f) : N.map f ≃ N ⧸ (N ⊓ f.ker).subgroupOf N := by
  symm
  let φ : N →* (N.map f) := {
    toFun := fun x => ⟨f x, by
      simp
      use x
      constructor
      · exact SetLike.coe_mem x
      · rfl⟩
    map_one' := by
      ext
      apply f.map_one'
    map_mul' := by
      intro x y
      ext
      apply f.map_mul'
  }
  haveI h' : Function.Surjective φ := by
    intro y
    dsimp [φ]
    have hy : y.1 ∈ Subgroup.map f N := by exact SetLike.coe_mem y
    obtain ⟨t, ht1, ht2⟩ := Subgroup.mem_map.1 hy
    use ⟨t, ht1⟩
    exact SetCoe.ext ht2
  haveI h1 : N ⧸ φ.ker ≃* (Subgroup.map f N) := by
    apply QuotientGroup.quotientKerEquivOfSurjective (G := N) (H := (N.map f)) (φ := φ) h'
  have h2 : φ.ker = (N ⊓ f.ker).subgroupOf N := by
    ext x
    constructor
    <;> intro hx
    · simp only [Subgroup.inf_subgroupOf_left]
      refine Subgroup.mem_subgroupOf.mpr ?h.mp.a
      rw [MonoidHom.mem_ker] at *
      exact (Submonoid.mk_eq_one (Subgroup.map f N).toSubmonoid).mp hx
    · simp only [Subgroup.inf_subgroupOf_left] at hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [MonoidHom.mem_ker] at *
      exact OneMemClass.coe_eq_one.mp hx
  rw [← h2]
  apply h1.toEquiv

set_option synthInstance.maxHeartbeats 100000000
#check Function.leftInverse_invFun

#check Subgroup.mem_subgroupOf
#check Subgroup.card_eq_card_quotient_mul_card_subgroup

open AlgEquiv AlgHom
#check AlgEquiv
#check AlgEquiv.restrictNormal
#check algebraMap K' L
#check Algebra.algebraMap_eq_smul_one
#check ofInjectiveField
#check algebraMap.coe_smul
#check algebraMap_smul

theorem AlgEquiv.restrictNormalHom_restrictScalarsHom {x : (L ≃ₐ[K'] L)} : AlgEquiv.restrictNormalHom K' (AlgEquiv.restrictScalarsHom K x) = 1 := by
  unfold restrictNormalHom restrictScalarsHom
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.mk'_apply]
  unfold restrictNormal restrictNormal' AlgHom.restrictNormal restrictNormalAux restrictScalars
  ext t
  rw [one_apply]
  simp only [toAlgHom_eq_coe, RingEquiv.toEquiv_eq_coe, AlgHom.coe_coe, coe_mk, EquivLike.coe_coe, coe_ringEquiv, coe_ofBijective, coe_comp, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply]
  -- #check x.commutes'
  -- have h1 : x ((ofInjectiveField (IsScalarTower.toAlgHom K K' L)) t) = ((ofInjectiveField (IsScalarTower.toAlgHom K K' L)) t) := by
  --   #check (ofInjectiveField (IsScalarTower.toAlgHom K K' L)).toAlgHom.toRingHom
  --   #check (IsScalarTower.toAlgHom K K' L).range
  -- haveI : Algebra K' (IsScalarTower.toAlgHom K K' L).range := by
  --   refine (ofInjectiveField (IsScalarTower.toAlgHom K K' L)).toAlgHom.toAlgebra
  have h1 : (ofInjectiveField (IsScalarTower.toAlgHom K K' L)) t = (ofInjectiveField (IsScalarTower.toAlgHom K K' L)).toAlgHom.toRingHom t := rfl
  rw [h1]
  -- haveI range : Subalgebra K' L := {
  --   carrier := (IsScalarTower.toAlgHom K K' L).range
  --   mul_mem' := ?mul_mem'
  --   one_mem' := ?one_mem'
  --   add_mem' := ?add_mem'
  --   zero_mem' := ?zero_mem'
  --   algebraMap_mem' := ?algebraMap_mem'
  -- }
  have h2 : ((ofInjectiveField (IsScalarTower.toAlgHom K K' L)).toAlgHom.toRingHom t) = algebraMap K' L t := rfl
  simp only [h2, commutes]
  -- simp only [toAlgHom_eq_coe]
  -- simp only [toRingHom_eq_coe]
  -- simp only [toAlgHom_toRingHom, commutes]
  simp only [← h2, RingHom.coe_coe, Subtype.coe_eta, toAlgHom_eq_coe, toRingHom_eq_coe, toAlgHom_toRingHom, RingHom.coe_coe, symm_apply_apply]
  -- rw [← h2, toAlgHom_eq_coe, toRingHom_eq_coe, toAlgHom_toRingHom, Subtype.coe_eta]
  -- rw [← h1]
  -- simp only [symm_apply_apply]
  -- have h1 : ∀ k : K', (ofInjectiveField (IsScalarTower.toAlgHom K K' L)) k = algebraMap K' (IsScalarTower.toAlgHom K K' L).range k := by
  --   intro k
  --   unfold algebraMap
  --   have h : (ofInjectiveField (IsScalarTower.toAlgHom K K' L)) k = (ofInjectiveField (IsScalarTower.toAlgHom K K' L)).toAlgHom.toAlgebra.toRingHom k := rfl
  --   rw [h, ← algebraMap, ← algebraMap]
  --   simp only [toAlgHom_eq_coe, toRingHom_eq_coe, toAlgHom_toRingHom,
  --     Algebra.algebraMap_eq_smul_one]
  --   congr
  -- have h2 : ∀ k : K', algebraMap K' (IsScalarTower.toAlgHom K K' L).range k = algebraMap K' L k := by
  --   intro k
  --   rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  --   sorry

  -- simp only [Algebra.algebraMap_eq_smul_one]

  -- -- have h3 : (1 : (IsScalarTower.toAlgHom K K' L).range) = (1 : L) :=

  -- haveI : Algebra K' (IsScalarTower.toAlgHom K K' L).range := by
  --   refine (ofInjectiveField (IsScalarTower.toAlgHom K K' L)).toAlgHom.toAlgebra
  -- have h4 : t • (1 : L) ∈ (IsScalarTower.toAlgHom K K' L).range := by
  --   simp only [mem_range, IsScalarTower.coe_toAlgHom']
  --   use t
  --   apply Algebra.algebraMap_eq_smul_one
  -- have h5 : (ofInjectiveField (IsScalarTower.toAlgHom K K' L)).symm ⟨t • (1 : L), h4⟩ = (ofInjectiveField (IsScalarTower.toAlgHom K K' L)).symm (t • (1 : (IsScalarTower.toAlgHom K K' L).range)) := by
  --   refine AlgEquiv.congr_arg ?_
  --   refine SetCoe.ext ?_
  --   simp only

  --   -- have : (↑(t • (1 : ((IsScalarTower.toAlgHom K K' L).range))) : L) = (t • ↑((1 : ((IsScalarTower.toAlgHom K K' L).range)) : L)) := by
  --   sorry

  -- have h6 : algebraMap K' _ t = (ofInjectiveField (IsScalarTower.toAlgHom K K' L)) t := by
  --   rw [h1, ← algebraMap]
  --   congr
  --   sorry
  -- rw [h5, ← Algebra.algebraMap_eq_smul_one, h6]
  -- exact symm_apply_apply (ofInjectiveField (IsScalarTower.toAlgHom K K' L)) t

  --simp only [_root_.map_one, smul_eq_mul, mul_one]
  --rw [map_smul (ofInjectiveField (IsScalarTower.toAlgHom K K' L)).symm t (1 : L)]
  -- have h3 : ∀ k : (IsScalarTower.toAlgHom K K' L).range, (ofInjectiveField (IsScalarTower.toAlgHom K K' L)).symm k = (ofInjectiveField (IsScalarTower.toAlgHom K K' L)).symm.toAlgEquiv k := by
  --   intro k
  --   rfl
  -- rw [h3 _, ← algebraMap]
  -- simp only [toAlgHom_eq_coe, toRingHom_eq_coe, toAlgHom_toRingHom]--, Algebra.algebraMap_eq_smul_one, ← SMul.smul_eq_hSMul]
  --rw [map_smul]

  --simp only [toAlgHom_eq_coe, toRingHom_eq_coe, toAlgHom_toRingHom, ← SMul.smul_eq_hSMul, Algebra.smul_def, mul_one]
  -- dsimp [restrictNormal, restrictNormal', AlgHom.restrictNormal, restrictScalars]
  -- ext t
  -- simp only [coe_ofBijective, coe_comp, AlgHom.coe_coe, Function.comp_apply, one_apply]

#check AlgEquiv.restrictScalars

theorem AlgEquiv.restrictNormal_ker_eq : (AlgEquiv.restrictNormalHom K').ker = (⊤ : Subgroup (L ≃ₐ[K'] L)).map (AlgEquiv.restrictScalarsHom K) := by
  ext x
  constructor
  · intro hx
    let x' : L ≃ₐ[K'] L := {
      x.toRingEquiv with
      commutes' := by
        intro r
        have h : r = AlgEquiv.restrictNormalHom K' x r := by
          rw [MonoidHom.mem_ker] at hx
          rw [hx, one_apply]
        nth_rw 2 [h]
        rw [AlgEquiv.restrictNormalHom]
        dsimp
        rw [AlgEquiv.restrictNormal_commutes]
    }
    rw [Subgroup.mem_map]
    use x'
    constructor
    · apply Subgroup.mem_top
    · exact rfl
    --rw [Subgroup.mem_map]
    --obtain ⟨f, hf⟩ := Function.surjective_iff_hasRightInverse.1 (AlgEquiv.restrictNormalHom_surjective L (F := K) (K₁ := K'))
  · sorry
  -- · intro hx
  --   refine (MonoidHom.mem_ker (restrictNormalHom K')).mpr ?h.mpr.a
  --   obtain ⟨t, ht1, ht2⟩ := Subgroup.mem_map.1 hx
  --   rw [← ht2, AlgEquiv.restrictNormalHom_restrictScalarsHom]


theorem lowerIndex_eq_of_subgroup_aux {t : L ≃ₐ[K] L} {k : L ≃ₐ[K'] L} (h : AlgEquiv.restrictScalarsHom K k = t) : i_[L/K] t = i_[L/K'] k := by
  unfold AlgEquiv.lowerIndex
  have h' : ∀ x : L, t x = k x := by
    intro x
    rw [← h]
    rfl
  have h'' : ⨆ x : vL.v.integer, vL.v (t x - x) = ⨆ x : vL.v.integer, vL.v (k x - x) := iSup_congr fun i ↦ congrArg (vL.v) (congrFun (congrArg HSub.hSub (h' ↑i)) (i : L))
  rw [h'']

#check lowerRamificationGroup_eq_decompositionGroup
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
      -- dsimp [f]
      -- simp only [Subtype.exists]
      -- use (AlgEquiv.restrictScalars K).invFun t
      -- have h : Function.invFun (AlgEquiv.restrictScalars K) ↑t ∈ G(L/K')_[⌈x⌉]:= by sorry
      -- use h
      --have h' : (AlgEquiv.restrictScalarsHom K) (Function.invFun (AlgEquiv.restrictScalars K (S := K')) t.1) = ((AlgEquiv.restrictScalarsHom K) ∘ (Function.invFun (AlgEquiv.restrictScalars K (S := K')))) t.1 := by sorry
  haveI h2: (Subgroup.map (AlgEquiv.restrictNormalHom K') G(L/K)_[⌈x⌉]) ≃ (G(L/K)_[⌈x⌉] ⧸ (G(L/K)_[⌈x⌉] ⊓ (AlgEquiv.restrictNormalHom K').ker).subgroupOf G(L/K)_[⌈x⌉]) := by
    apply Subgroup_map
    exact AlgEquiv.restrictNormalHom_surjective L
  haveI h3 : (G(L/K')_[⌈x⌉].map (AlgEquiv.restrictScalarsHom K)) = (G(L/K)_[⌈x⌉] ⊓ (AlgEquiv.restrictNormalHom K').ker) := by
    ext t
    constructor
    <;> intro ht
    · apply Subgroup.mem_inf.2
      constructor
      · rw [(RamificationGroup_iff_Subgroup_aux K K' L ?_ hgen hgen'), Subgroup.mem_inf] at ht
        apply ht.1
        apply Int.ceil_nonneg hx
      · sorry
      -- · apply (MonoidHom.mem_ker (AlgEquiv.restrictNormalHom K')).2
      --   obtain ⟨y, _, hy2⟩ := Subgroup.mem_map.1 ht
      --   rw [← hy2]
      --   apply AlgEquiv.restrictNormalHom_restrictScalarsHom
    · --apply Subgroup.mem_map.2
      --rw [Subgroup.mem_inf] at ht
      rw [AlgEquiv.restrictNormal_ker_eq] at ht
      apply (RamificationGroup_iff_Subgroup_aux K K' L ?_ hgen hgen').2 ht
      apply Int.ceil_nonneg hx
  rw [Nat.card_congr h1, Nat.card_congr h2, h3]
  have h4 : Nat.card (↥ G(L/K)_[⌈x⌉] ⧸ ( G(L/K)_[⌈x⌉] ⊓ (AlgEquiv.restrictNormalHom K').ker).subgroupOf G(L/K)_[⌈x⌉] ) * Nat.card ((G(L/K)_[⌈x⌉] ⊓ (AlgEquiv.restrictNormalHom K').ker).subgroupOf G(L/K)_[⌈x⌉])= Nat.card (G(L/K)_[⌈x⌉]) := by
    -- haveI : Fintype (G(L/K)_[⌈x⌉] ⧸ ( G(L/K)_[⌈x⌉] ⊓ (AlgEquiv.restrictNormalHom K').ker).subgroupOf G(L/K)_[⌈x⌉] ) := by exact (( G(L/K)_[⌈x⌉] ⊓ (AlgEquiv.restrictNormalHom K').ker).subgroupOf G(L/K)_[⌈x⌉] ).fintypeQuotientOfFiniteIndex
    -- haveI : Fintype (( G(L/K)_[⌈x⌉] ⊓ (AlgEquiv.restrictNormalHom K').ker).subgroupOf G(L/K)_[⌈x⌉] ) := by exact Fintype.ofFinite ↥(( G(L/K)_[⌈x⌉] ⊓ (AlgEquiv.restrictNormalHom K').ker).subgroupOf G(L/K)_[⌈x⌉] )
    -- haveI : Fintype G(L/K)_[⌈x⌉] := by exact Fintype.ofFinite ↥ G(L/K)_[⌈x⌉]
    -- rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    symm
    apply Subgroup.card_eq_card_quotient_mul_card_subgroup
  rw [← h4]
  congr 1
  rw [Nat.card_congr]
  -- have h : ∀ t : G(L/K)_[⌈x⌉], (t : (L ≃ₐ[K] L)) ∈ ((AlgEquiv.restrictNormalHom K').ker) ↔ t ∈ ((AlgEquiv.restrictNormalHom K').ker).subgroupOf G(L/K)_[⌈x⌉] := by
  --   intro t
  --   symm
  --   apply Subgroup.mem_subgroupOf (H := (AlgEquiv.restrictNormalHom K').ker) (K := G(L/K)_[⌈x⌉]) (h := t)
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

open LocalRing ExtDVR

#check IsScalarTower.algebraMap_eq

variable [IsScalarTower 𝒪[K] 𝒪[K'] 𝒪[L]]
theorem RamificationGroup_card_zero_comp_aux : (Nat.card G(K'/K)_[0] : ℝ) * (Nat.card G(L/K')_[0] : ℝ) = (Nat.card G(L/K)_[0] : ℝ) := by
  repeat rw [RamificationIdx_eq_card_of_inertia_group]
  norm_cast
  unfold LocalField.ramificationIdx IsLocalRing.ramificationIdx
  let e_K'K := Ideal.ramificationIdx (algebraMap ↥𝒪[K] ↥𝒪[K']) (IsLocalRing.maximalIdeal ↥𝒪[K]) (IsLocalRing.maximalIdeal ↥𝒪[K'])
  let e_LK' := Ideal.ramificationIdx (algebraMap ↥𝒪[K'] ↥𝒪[L]) (IsLocalRing.maximalIdeal ↥𝒪[K']) (IsLocalRing.maximalIdeal ↥𝒪[L])
  let e_LK := Ideal.ramificationIdx (algebraMap ↥𝒪[K] ↥𝒪[L]) (IsLocalRing.maximalIdeal ↥𝒪[K]) (IsLocalRing.maximalIdeal ↥𝒪[L])
  have h : (IsLocalRing.maximalIdeal 𝒪[L]) ^ (e_K'K * e_LK') = (IsLocalRing.maximalIdeal 𝒪[L]) ^ (e_LK) := by
    dsimp [e_K'K, e_LK', e_LK]
    sorry
    -- rw [← maximalIdeal_map_eq_maximalIdeal_pow_ramificationIdx (IsValExtension.integerAlgebra_injective K L), mul_comm, pow_mul, ← maximalIdeal_map_eq_maximalIdeal_pow_ramificationIdx (IsValExtension.integerAlgebra_injective K' L), ← Ideal.map_pow, ← maximalIdeal_map_eq_maximalIdeal_pow_ramificationIdx (IsValExtension.integerAlgebra_injective K K'), Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  sorry

#check Ideal.isPrime_iff_bot_or_prime
#check Ideal.pow_mem_pow
#check Real.instFloorRing
theorem Int.ceil_eq_ceil {a b : ℝ} (h : a ≤ b) (h' : b - a ≤ ⌈a⌉ - a) : ⌈b⌉ = ⌈a⌉ := by
  sorry
  -- by_contra hc
  -- have h : ⌈a⌉ < b := by
  --   apply lt_of_le_of_lt (b := (⌈b⌉ - 1 : ℝ))
  --   norm_cast
  --   push_neg at hc
  --   apply Int.le_sub_one_of_lt (lt_of_le_of_ne (Int.ceil_le_ceil a b h) hc.symm)
  --   rw [sub_lt_iff_lt_add]
  --   apply Int.ceil_lt_add_one
  -- simp only [tsub_le_iff_right, sub_add_cancel] at h'
  -- absurd h'
  -- push_neg
  -- exact_mod_cast h


open Asymptotics Filter intervalIntegral MeasureTheory

#check eq_of_has_deriv_right_eq
#check ContinuousLinearMap.smulRight
#check phi_eq_sum_card
#check intervalIntegral.sum_integral_adjacent_intervals
#check MeasureTheory.integral_union
#check Finset.sum_equiv



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
  · --rw [hu', phiReal_zero_eq_zero]
    simp only [hu', integral_same, one_div, Int.ceil_zero, zero_sub, Int.reduceNeg, neg_lt_self_iff, zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, CharP.cast_eq_zero, Left.neg_nonpos_iff, zero_le_one, max_eq_left, Int.cast_zero, sub_self, zero_mul, add_zero, mul_zero]
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
                    -- · apply Int.ceil_le_ceil
                  --   apply le_of_lt (lt_of_le_of_lt (Set.mem_Ioc.1 hx).2 (by linarith [Int.ceil_lt_add_one u]))
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
          -- apply IntegrableOn.congr_fun_ae (f := fun x => (Nat.card G(L/K)_[(⌈u⌉)] : ℝ) / (Nat.card G(L/K)_[0] : ℝ))
          -- apply integrableOn_const.2
          -- right
          -- dsimp [μ]
          -- exact measure_Ioc_lt_top
          -- unfold phiDerivReal EventuallyEq
          -- apply (ae_restrict_iff_subtype _).2
          -- apply ae_of_all
          -- intro ⟨a, ha⟩
          -- have ha' : ⌈a⌉ = ⌈u⌉ := by
          --   apply Int.ceil_eq_iff.2
          --   refine ⟨(Set.mem_Ioc.1 ha).1, le_trans (Set.mem_Ioc.1 ha).2 (Int.le_ceil u)⟩
          -- dsimp
          -- rw [ha', max_eq_right]
          -- exact Int.ceil_nonneg hu
          -- exact measurableSet_Ioc
        · linarith [Int.ceil_lt_add_one u]
        · rw [sub_nonneg, ← (Int.cast_one (R := ℝ)), Int.cast_le]
          apply Int.one_le_ceil_iff.2
          apply lt_of_le_of_ne hu
          exact fun a ↦ hu' (id (Eq.symm a))
        · exact hu
        -- have h' : Set.Ioc 0 (⌈u⌉ - 1 : ℝ) = ⋃ (i ∈ Set.Icc 0 (⌈u⌉ - 1)), Set.Ioc (i : ℝ) (i + 1 : ℝ) := by
        --   ext x
        --   constructor
        --   <;> intro hx
        --   · apply Set.mem_iUnion.2
        --     use ⌈x⌉ - 1
        --     simp only [Set.mem_Icc, sub_nonneg, tsub_le_iff_right, sub_add_cancel, Int.cast_le,
        --       Set.mem_iUnion, Set.mem_Ioc, exists_and_left, exists_prop]
        --     sorry
        --   · simp only [Set.mem_Ioc]
        --     sorry
        -- rw [h']
        -- apply (integrableOn_finite_biUnion _).2
        -- intro i hi
        -- apply IntegrableOn.congr_fun_ae (f := fun x => (Nat.card G(L/K)_[⌈i + 1⌉] : ℝ) / (Nat.card G(L/K)_[0] : ℝ))
        -- apply integrableOn_const.2
        -- right
        -- dsimp [μ]
        -- exact measure_Ioc_lt_top
        -- unfold phiDerivReal EventuallyEq
        -- apply (ae_restrict_iff_subtype _).2
        -- apply ae_of_all
        -- intro a
        -- dsimp
        -- obtain ⟨a, ha⟩ := a
        -- simp only
        -- rw [max_eq_right]
        -- obtain ⟨ha1, ha2⟩ := Set.mem_Ioc.1 ha
        -- have h' : ⌈a⌉ = (i + 1) := by sorry
        -- rw [h']
        -- apply Int.ceil_nonneg
        -- obtain ⟨ha1, ha2⟩ := Set.mem_Ioc.1 ha
        -- obtain ⟨hi1, h12⟩ := Set.mem_Icc.1 hi
        -- apply le_of_lt
        -- apply lt_of_le_of_lt (b := (i : ℝ))
        -- simp only [Int.cast_nonneg, hi1]
        -- simp only [ha1]
        -- exact measurableSet_Ioc
        -- exact Set.finite_Icc 0 (⌈u⌉ - 1)
        -- apply IntegrableOn.congr_fun_ae (f := fun x => (Nat.card G(L/K)_[(⌈u⌉)] : ℝ) / (Nat.card G(L/K)_[0] : ℝ))
        -- apply integrableOn_const.2
        -- right
        -- dsimp [μ]
        -- exact measure_Ioc_lt_top
        -- unfold phiDerivReal EventuallyEq
        -- apply (ae_restrict_iff_subtype _).2
        -- apply ae_of_all
        -- intro a
        -- dsimp
        -- obtain ⟨a, ha⟩ := a
        -- simp only
        -- obtain ⟨ha1, ha2⟩ := Set.mem_Ioc.1 ha
        -- rw [max_eq_right]
        -- have h' : ⌈a⌉ = ⌈u⌉ := by
        --   apply Int.ceil_eq_iff.2
        --   constructor
        --   · exact ha1
        --   · apply le_trans ha2
        --     exact Int.le_ceil u
        -- rw [h']
        -- sorry
        -- -- apply eventuallyEq_iff_exists_mem.2
        -- -- use Set.Icc 0 (⌈u⌉ - 1 : ℝ)
        -- -- constructor
        -- -- · apply ae_of_all

        -- exact measurableSet_Ioc
        -- rw [sub_le_iff_le_add]
        -- apply le_of_lt (Int.ceil_lt_add_one u)
        -- sorry
        -- exact hu
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
        --simp only [Pi.one_apply]
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
          -- rw [integral_congr (g := fun x => (Nat.card ↥ G(L/K)_[(i a)] : ℝ) / (Nat.card ↥ G(L/K)_[0] : ℝ))]
          -- rw [intervalIntegral.integral_const' (a := a) (b := ↑(a + 1)) ((Nat.card G(L/K)_[(i a)] : ℝ) / (Nat.card G(L/K)_[0] : ℝ))]
          -- dsimp [μ]
          -- simp only [Nat.cast_add, Nat.cast_one, Real.volume_Ioc, add_sub_cancel_left, ENNReal.ofReal_one, ENNReal.one_toReal, add_lt_iff_neg_left, not_lt, zero_le_one, Set.Ioc_eq_empty, measure_empty, ENNReal.zero_toReal, sub_zero, one_mul]
          -- dsimp [Set.EqOn]
          -- intro x hx
          -- dsimp [phiDerivReal, i]
          -- sorry
          -- it's wrong!!!
          -- obtain ⟨hx1, hx2⟩ := Set.mem_uIcc.1 hx
          -- have h' : ⌈x⌉ = a + 1 := by
          --   sorry
          -- rw [max_eq_right, h']
          -- rw [h']
          -- exact Int.le.intro_sub (a + 1 + 0) rfl
          -- rw [max_eq_right]
          -- sorry
          -- sorry
          -- nth_rw 1 [← Nat.sub_zero (⌈u⌉ - 1).toNat]
          -- have h : ∑ k in Finset.range ((⌈u⌉ - 1).toNat - 0), ∫ x in (k : ℝ)..(k + 1 : ℝ), phiDerivReal K L x ∂μ = ∑ k in Finset.range ((⌈u⌉ - 1).toNat - 0), ∫ x in (↑(0 + k) : ℝ)..(↑(0 + k) + 1 : ℝ), phiDerivReal K L x ∂μ := by simp only [zero_add]
          -- simp only [h, zero_add]
          -- simp only [← (Finset.sum_Ico_eq_sum_range (fun k =>  ∫ (x : ℝ) in (k : ℝ)..(k + 1 : ℝ), phiDerivReal K L x ∂μ ) 0 (⌈u⌉ - 1).toNat)]
          -- let e : ℤ ≃ ℤ := {
          --   toFun := fun x => x + 1
          --   invFun := fun x => x - 1
          --   left_inv := fun x => by simp only [← add_sub, sub_self, add_zero]
          --   right_inv := fun x => by simp only [sub_add_cancel]
          -- }
          -- apply Finset.sum_equiv e
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
          --   apply integral_congr
          --   dsimp [Set.EqOn]
          --   intro x hx
          --   have h : ⌈x⌉ = ⌈u⌉ := by
          --     sorry
          --   rw [phiDerivReal, h, max_eq_right]
          --   apply Int.ceil_nonneg hu
          -- rw [h, intervalIntegral.integral_const, smul_eq_mul, max_eq_right, one_div, inv_mul_eq_div, Int.cast_sub, Int.cast_one, mul_div]
          -- sorry
  --rw [← intervalIntegral.sum_integral_adjacent_intervals (f := phiDerivReal K L) (μ := μ) (a := 1)]

theorem phiReal_eq_phi {u : ℚ} (hu : 0 ≤ u) : phiReal K L u = phi K L u := by
  by_cases hu' : u = 0
  · simp only [hu', phi_zero_eq_zero, Rat.cast_zero, phiReal_zero_eq_zero]
  sorry
  -- · rw [phiReal_eq_sum_card K L, phi_eq_sum_card]
  --   simp only [one_div, Rat.ceil_cast, Nat.cast_sum, Int.cast_max, Int.cast_zero, Int.cast_sub, Int.cast_one, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, Rat.cast_add, Rat.cast_sum, Rat.cast_sub, Rat.cast_max, Rat.cast_zero, Rat.cast_intCast, Rat.cast_one]
  --   apply lt_of_le_of_ne hu
  --   exact fun a ↦ hu' (id (Eq.symm a))
  --   exact Rat.cast_nonneg.mpr hu


#check MeasureTheory.volume

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
  -- rw [integral_of_ge hu]
  -- have h1 : u - 0 = ∫ (x : ℝ) in Set.Ioc 0 u, 1 := by
  --   simp only [sub_zero, MeasureTheory.integral_const, MeasurableSet.univ,
  --     MeasureTheory.Measure.restrict_apply, Set.univ_inter, Real.volume_Ioc, zero_sub, smul_eq_mul, mul_one]
  --   sorry
  -- rw [← sub_zero u, h1, ← MeasureTheory.integral_neg]
  -- apply integral_congr


--for Mathlib
theorem Finset.Icc_union_Icc_eq_Icc {a b c : ℤ} (h : a ≤ b) (h' : b ≤ c) : Finset.Icc a b ∪ Finset.Icc (b + 1) c = Finset.Icc a c := by
  ext x
  constructor
  <;> intro hx
  · simp only [mem_union, mem_Icc] at *
    match hx with
        | Or.inl hx =>
                      refine ⟨hx.1, le_trans hx.2 h'⟩
        | Or.inr hx =>
                      refine ⟨by linarith [h, hx], hx.2⟩
  · simp only [mem_union, mem_Icc] at *
    by_cases hx' : x ≤ b
    · left
      refine ⟨hx.1, hx'⟩
    · right
      refine ⟨by linarith [hx'], hx.2⟩

#check Finset.sum
#check Set.Icc_union_Icc_eq_Icc
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
        sorry --apply Ramification_Group_card_pos
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
          sorry --exact Int.ceil_le_ceil u v h
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
--   rw [phiReal_eq_sum_card, phiReal_eq_sum_card]
--   -- have h1 : (∑ x ∈ Finset.Icc 1 (⌈v⌉ - 1), Nat.card ↥ G(L/K)_[x]) - (∑ x ∈ Finset.Icc 1 (⌈u⌉ - 1), Nat.card ↥ G(L/K)_[x]) ≤ ∑ x ∈ Finset.Icc ⌈u⌉ (⌈v⌉ - 1), Nat.card G(L/K)_[⌈u⌉] := by sorry
--   calc
--     _ ≤  1 / (Nat.card G(L/K)_[0] ) * (∑ x ∈ Finset.Icc ⌈u⌉ (⌈v⌉ - 1), Nat.card G(L/K)_[⌈u⌉] + (v - (max 0 (⌈v⌉ - 1))) * (Nat.card G(L/K)_[⌈v⌉]) - (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈u⌉])) := by
--       have h : Finset.Icc 1 (⌈v⌉ - 1) = Finset.Icc 1 (⌈u⌉ - 1) ∪ Finset.Icc ⌈u⌉ (⌈v⌉ - 1) := by sorry
--       rw [h, Finset.sum_union, ← mul_sub, add_comm, ← sub_sub]
--       rw [add_comm (∑ x ∈ Finset.Icc 1 (⌈u⌉ - 1), Nat.card ↥ G(L/K)_[x]), Nat.cast_add, ← add_assoc, mul_le_mul_left, add_sub_cancel_right, add_comm, ← add_sub, ← add_sub, add_le_add_iff_right, Nat.cast_le]
--       apply Finset.sum_le_sum
--       sorry
--       sorry
--       sorry
--     _ =  1 / (Nat.card G(L/K)_[0] ) * ((⌈v⌉ - ⌈u⌉) * Nat.card G(L/K)_[⌈u⌉] + (v - (max 0 (⌈v⌉ - 1))) * (Nat.card G(L/K)_[⌈v⌉]) - (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈u⌉])) := by
--       congr
--       simp only [Finset.sum_const, Int.card_Icc, sub_add_cancel, smul_eq_mul, Nat.cast_mul, mul_eq_mul_right_iff, Nat.cast_eq_zero]
--       left
--       norm_cast
--       rw [Int.toNat_of_nonneg]
--       sorry
--     _ ≤ _ := by
--       unfold phiDerivReal
--       sorry
--   sorry
--   sorry

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
          sorry -- apply (Decidable.not_and_iff_or_not (⌈u⌉ < a) (a ≤ ⌈v⌉ - 1)).mpr ?_
          -- left
          -- push_neg
          -- exact ha.2
        rw [h1, Finset.sum_union hd, add_comm, Nat.cast_add, add_sub_assoc, sub_self, add_zero]
        rw [Finset.sum_union hd, add_comm, Nat.cast_add, add_sub_assoc, sub_self, add_zero, Nat.cast_le]
        apply Finset.sum_le_sum
        intro i hi
        apply Nat.card_mono
        exact Set.toFinite (G(L/K)_[i] : Set (L ≃ₐ[K] L))
        apply lowerRamificationGroup.antitone
        apply le_trans (Finset.mem_Ioc.1 hi).2 (by linarith)
        -- push_neg
        -- intro ha'
      -- rw [sub_le_sub_iff_right, add_le_add_iff_right, Nat.cast_le]
      -- apply Finset.sum_le_sum
      -- intro i hi
      -- apply Nat.card_mono
      -- exact Set.toFinite (G(L/K)_[i] : Set (L ≃ₐ[K] L))
      -- apply lowerRamificationGroup.antitone
      -- apply le_trans (Finset.mem_Icc.1 hi).2 (by linarith)
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
    -- _ ≤ (∑ x ∈ Finset.Icc 1 (⌈v⌉ - 1), Nat.card G(L/K)_[x]) + (v - (⌈v⌉ - 1)) * (Nat.card G(L/K)_[⌈v⌉]) - ((∑ x ∈ Finset.Icc 1 ⌈u⌉, Nat.card G(L/K)_[x]) - (⌈u⌉ - u) * (Nat.card ↥ G(L/K)_[⌈u⌉])) := by sorry
      -- rw [sub_le_sub_iff_left, sub_le_sub_iff_right, Nat.cast_le]
      -- --turn this into a thm
      -- apply Finset.sum_le_sum
      -- intro i hi
      -- apply Nat.card_mono
      -- exact Set.toFinite (G(L/K)_[⌈v⌉] : Set (L ≃ₐ[K] L))
      -- apply lowerRamificationGroup.antitone
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
  sorry -- apply Ramification_Group_card_pos
  apply le_of_lt hu
  apply le_of_lt (lt_of_lt_of_le hu h)


--already done!!!!!
theorem phiReal_StrictMono : StrictMono (phiReal K L) := by sorry
  -- intro a b hab
  -- by_cases hb : b ≤ 0
  -- · sorry
  -- · have h : 0 < phiReal K L b - phiReal K L a := by
  --     apply lt_of_lt_of_le ?_ (le_phiReal_sub_phiReal K L (le_of_lt hab))
  --     apply mul_pos (by linarith [hab])
  --     sorry
  --   linarith [h]

theorem phiReal_injective {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : Function.Injective (phiReal K L) := by
  intro a1 a2 h
  contrapose! h
  by_cases h1 : a1 > a2
  · apply ne_of_gt (phiReal_StrictMono K L h1)
  · push_neg at *
    apply ne_of_lt (phiReal_StrictMono K L (lt_of_le_of_ne h1 h))

-- theorem phiReal_Bijective_section_aux {n : ℤ} {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : ∀ (y : ℝ) , (phiReal K L n) ≤ y ∧ y < (phiReal K L (n + 1)) → ∃ (x : ℝ), phiReal K L x = y := by sorry

-- theorem phiReal_infty_aux (y : ℝ) : ∃ n : ℤ, phiReal K L n ≤ y ∧ y < phiReal K L (n + 1) := by
--   sorry

-- theorem phiReal_bijective {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : Function.Bijective (phiReal K L) := by
--   constructor
--   · intro a1 a2 h
--     contrapose! h
--     by_cases h1 : a1 > a2
--     · apply ne_of_gt (phiReal_StrictMono K L h1)
--     · push_neg at *
--       apply ne_of_lt (phiReal_StrictMono K L (lt_of_le_of_ne h1 h))
--   · intro y
--     obtain ⟨n, hn⟩ := phiReal_infty_aux K L y
--     apply phiReal_Bijective_section_aux K L (n := n) hgen y hn

theorem phiReal_phi_ceil_eq_aux {u : ℝ} (hu : 0 ≤ u) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : ∃ u' : ℚ, ⌈u⌉ = ⌈u'⌉ ∧ ⌈phiReal K L u⌉ = ⌈phi K L u'⌉ := by
  by_cases hc : u = ⌈u⌉
  · use ⌈u⌉
    constructor
    · exact Eq.symm (Int.ceil_intCast ⌈u⌉)
    · rw [hc, Int.ceil_intCast ⌈u⌉,← Rat.cast_intCast, phiReal_eq_phi K L (u := ⌈u⌉), Rat.ceil_cast]
      apply Int.cast_nonneg.mpr (Int.ceil_nonneg hu)
  · by_cases hc' : phiReal K L u = ⌈phiReal K L u⌉
    · have h : ∃ u' : ℚ, u' = u := by
        have h' : ∃ u' : ℚ, phi K L u' = ⌈phiReal K L u⌉ := by apply (phi_Bijective K L).2
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
        -- have h1 : (Set.Ici u ∩ Set.Icc u ⌈u⌉ ∩ Set.Icc u (u + ⌈phiReal K L u⌉ - (phiReal K L u))).Nonempty := by
        --   use u
        --   constructor
        --   · constructor
        --     · exact Set.left_mem_Ici
        --     · apply Set.mem_Icc.2
        --       refine ⟨by linarith, Int.le_ceil u⟩
        --   · apply Set.mem_Icc.2
        --     constructor
        --     linarith
        --     linarith [Int.le_ceil (phiReal K L u)]
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
            sorry --apply Ramification_Group_card_pos
            exact hc''
          · have h : u' - u = 0 := by
              apply Eq.symm (eq_of_le_of_not_lt (by linarith [hu'1]) hc'')
            rw [h, zero_mul, zero_mul]
          exact hu'3
        apply_mod_cast Eq.symm (Int.ceil_eq_ceil _ h)
        apply (phiReal_StrictMono K L).monotone hu'1
        apply Rat.cast_nonneg.1 (le_trans hu hu'1)
      -- · by_contra hcon
      --   have h : ⌈u⌉ < u' := by sorry
      --   simp only [tsub_le_iff_right, sub_add_cancel] at hu'2
      --   absurd hu'2
      --   push_neg
      --   exact_mod_cast h
      -- · rw [← Rat.ceil_cast (α := ℝ), ← phiReal_eq_phi K L (u := u')]
      --   have h : phiReal K L u' - phiReal K L u ≤ ⌈phiReal K L u⌉ - phiReal K L u := by sorry
      --   by_contra hcon
      --   have h' : ⌈phiReal K L u⌉ < phiReal K L u' := by sorry
      --   simp only [tsub_le_iff_right, sub_add_cancel] at h
      --   absurd h
      --   push_neg
      --   exact_mod_cast h'

variable [Algebra (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable K' L] [CompleteSpace K'] [CompleteSpace K]
theorem herbrand_Real (u : ℝ) (hu : 0 ≤ u) {gen : 𝒪[K']} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) {gen' : 𝒪[L]} (hgen' : Algebra.adjoin 𝒪[K] {gen'} = ⊤) {gen'' : 𝒪[L]} (hgen'' : Algebra.adjoin 𝒪[K'] {gen''} = ⊤) : G(L/K)_[⌈u⌉].map (AlgEquiv.restrictNormalHom K') = G(K'/K)_[⌈phiReal K' L u⌉] := by sorry
  -- obtain ⟨u', hu'1, hu'2⟩ := phiReal_phi_ceil_eq_aux K' L (u := u) hu hgen''
  -- rw [hu'1, hu'2]
  -- apply herbrand (K := K) (K' := K') (L := L) u' hgen hgen'


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
    sorry --apply phiReal_nonneg K' L hu
    simp only [Int.cast_max, Int.cast_zero, le_max_iff, le_refl, Int.cast_nonneg, true_or]
  · rw [← Int.ceil_zero (α := ℝ), ← RamificationGroup_card_comp_aux K K' L (by linarith) hgen hgen', mul_comm]
    congr 1
    sorry -- rw [herbrand_Real K K' L _ (by linarith) hgen'' hgen''' hgen', phiReal_zero_eq_zero]

-- #check Filter.le_iff_forall_inf_principal_compl
-- #check tendsto_nhds_of_eventually_eq

-- theorem phiReal_comp_of_isValExtension {u : ℝ} : ((phiReal K K') ∘ (phiReal K' L)) u = phiReal K L u := by
--   have hdf : ∀ x ∈ Set.Ico (⌊u⌋ : ℝ) (⌊u⌋ + 1 : ℝ), HasDerivWithinAt (phiReal K K' ∘ phiReal K' L) (phiDerivReal K L x) (Set.Ici x) x := by
--     intro x hx
--     unfold HasDerivWithinAt HasDerivAtFilter
--     haveI h : HasFDerivAtFilter (𝕜 := ℝ) ((phiReal K K') ∘ (phiReal K' L)) (ContinuousLinearMap.smulRight (S := ℝ) 1 (phiDerivReal K L x)) x (nhdsWithin x (Set.Ici x)) := {
--       isLittleO := by
--         dsimp
--         rw [IsLittleO_def]
--         intro c hc
--         rw [IsBigOWith_def, eventually_iff]
--         refine mem_nhdsWithin_Ici_iff_exists_Ico_subset.mpr ?_
--         use (⌊u⌋ + 1)
--         constructor
--         · apply Set.mem_Ioi.2
--           rw [Set.mem_Ico] at hx
--           exact hx.2
--         · rw [Set.subset_def]
--           intro y hy
--           dsimp
--           -- have h1 : phiReal K K' (phiReal K' L y) - phiReal K K' (phiReal K' L x) ≤ (phiReal K' L y - phiReal K' L x) * phiDerivReal K K' (phiReal K' L x) := by
--           --   apply phiReal_sub_phiReal_le μ K K' (v := phiReal K' L y) (u := phiReal K' L x)
--           --   sorry
--           -- have h2 : phiReal K' L y - phiReal K' L x ≤ (y - x) * phiDerivReal K' L (x) := by
--           --   apply phiReal_sub_phiReal_le μ K' L
--           --   sorry
--           have h1 : phiReal K K' (phiReal K' L y) - phiReal K K' (phiReal K' L x) ≤ (y - x) * (phiDerivReal K' L x) * phiDerivReal K K' (phiReal K' L x) := by
--             apply le_trans (phiReal_sub_phiReal_le K K' (u := phiReal K' L x) (v := phiReal K' L y) ?_ ?_)
--             apply (mul_le_mul_right ?_).2
--             apply phiReal_sub_phiReal_le K' L (u := x) (v := y) ?_
--             obtain ⟨hy1, hy2⟩ := Set.mem_Ico.1 hy
--             repeat sorry
--           have h2 : (y - x) * (phiDerivReal K' L y) * phiDerivReal K K' (phiReal K' L y) ≤ phiReal K K' (phiReal K' L y) - phiReal K K' (phiReal K' L x) := by sorry
--           rw [mul_assoc, phiDerivReal_comp] at h1
--           rw [mul_assoc, phiDerivReal_comp] at h2
--           have h3 : (y - x) * phiDerivReal K L x - (phiReal K K' (phiReal K' L y) - phiReal K K' (phiReal K' L x)) ≤ (y - x) * phiDerivReal K L x - (y - x) * phiDerivReal K L y := by sorry
--           have h4 : |phiReal K K' (phiReal K' L y) - phiReal K K' (phiReal K' L x) - (y - x) * phiDerivReal K L x| ≤ |(y - x) * phiDerivReal K L x - (y - x) * phiDerivReal K L y| := by sorry
--           apply le_trans h4
--           sorry
--     }
--     exact h
--   have hdg : ∀ x ∈ Set.Ico (⌊u⌋ : ℝ) (⌊u⌋ + 1 : ℝ), HasDerivWithinAt (phiReal K L) (phiDerivReal K L x) (Set.Ici x) x := by
--     intro x hx
--     unfold HasDerivWithinAt HasDerivAtFilter
--     haveI h : HasFDerivAtFilter (𝕜 := ℝ) (phiReal K L) (ContinuousLinearMap.smulRight (S := ℝ) 1 (phiDerivReal K L x)) x (nhdsWithin x (Set.Ici x)) := {
--       isLittleO := by
--         dsimp
--         rw [IsLittleO_def]
--         intro c hc
--         rw [IsBigOWith_def, eventually_iff]
--         refine mem_nhdsWithin_Ici_iff_exists_Ico_subset.mpr ?_
--         use (⌊u⌋ + 1)
--         constructor
--         · apply Set.mem_Ioi.2
--           rw [Set.mem_Ico] at hx
--           exact hx.2
--         · rw [Set.subset_def]
--           intro y hy
--           dsimp
--           sorry
--           -- by_cases hcase : 0 ≤ x
--           -- · have hcase' : 0 ≤ y := by sorry
--           --   have h : ⌈x⌉ = ⌈y⌉ := by sorry
--           --   rw [phiReal_eq_sum_card K L (le_of_lt hcase) phiReal_eq_sum_card K L (le_of_lt hcase'), phiDerivReal, h, max_eq_right, max_eq_right]
--           --   ring
--           --   simp only [abs_zero, hc, mul_nonneg_iff_of_pos_left, abs_nonneg]
--           --   exact Int.ceil_nonneg hcase'
--           --   sorry
--           -- · push_neg at hcase
--           --   have hcase' : y < 0 := by sorry
--           --   rw [phiReal_eq_self_of_le_zero K L (le_of_lt hcase), phiReal_eq_self_of_le_zero K L (le_of_lt hcase'), phiDerivReal, max_eq_left, div_self]
--           --   ring
--           --   simp only [abs_zero, hc, mul_nonneg_iff_of_pos_left, abs_nonneg]
--           --   · sorry
--           --   · refine Int.ceil_le.mpr ?_
--           --     rw [Int.cast_zero]
--           --     exact le_of_lt hcase
--     }
--     exact h
--   have hcf : ContinuousOn (phiReal K K' ∘ phiReal K' L) (Set.Icc (⌊u⌋) (⌊u⌋ + 1)) := by
--     sorry
--   have hcg : ContinuousOn (phiReal K L) (Set.Icc (⌊u⌋) (⌊u⌋ + 1)) := by
--     dsimp [ContinuousOn, ContinuousWithinAt]
--     intro x hx
--     apply tendsto_nhds_of_eventually_eq
--     use {x}
--     constructor
--     · refine mem_nhds_iff.mpr ?h.left.a
--       use {x}
--       constructor
--       · rfl
--       · constructor
--         · sorry
--         · rfl
--     use Set.Icc (⌊u⌋ : ℝ) (⌊u⌋ + 1 : ℝ)
--     constructor
--     · apply mem_principal_self
--     · have h : {x} ∩ Set.Icc (↑⌊u⌋) (↑⌊u⌋ + 1) = {x} := by sorry
--       simp only [h]
--       ext t
--       constructor
--       · intro ht
--         sorry
--       · intro ht
--         sorry
    -- rw [eventually_iff]
    -- have h : {x_1 | phiReal K L x_1 = phiReal K L x} = {x} := by
    --   ext t
    --   constructor
    --   · simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    --     sorry
    --   · simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
    --     intro h
    --     rw [h]
    -- rw [h]
    -- dsimp [nhdsWithin]
    -- apply mem_inf_of_left
    -- rw [nhds, Filter.mem_iInf]
    --apply Filter.le_iff_forall_inf_principal_compl.2
  --apply eq_of_has_deriv_right_eq hdf hdg hcf hcg
  --------------------------------------------------------------------------------------
  -- · rw [Function.comp_apply, phiReal, phiReal, phiReal]

  --   sorry
  -- simp only [Set.mem_Icc]
  -- constructor
  -- · exact Int.floor_le u
  -- · sorry



-- theorem phiReal_comp_of_isValExtension' : (phiReal K K') ∘ (phiReal K' L) = phiReal K L := by
--   apply eq_of_fderiv_eq (𝕜 := ℝ) (x := 0)
--   · rw [Function.comp_apply, phiReal_zero_eq_zero, phiReal_zero_eq_zero, phiReal_zero_eq_zero]
--   · apply Differentiable.comp (phiReal_Defferentiable K K') (phiReal_Defferentiable K' L)
--   · apply phiReal_Defferentiable
--   · intro x
--     conv =>
--       right
--       rw [HasFDerivAt.fderiv (x := x) (by apply phiReal_hasDeriv K L)]
--     ext
--     rw [fderiv_deriv, deriv.comp, HasDerivAt.deriv (x := x) (by apply phiReal_hasDeriv K' L), HasDerivAt.deriv (x := (phiReal K' L x)) (by apply phiReal_hasDeriv K K')]
--     -- conv =>
--     --   enter [1, 2]
--     --   rw [HasDerivAt.deriv]
--     -- rw [fderiv.comp, HasFDerivAt.fderiv (x := x) (by apply phiReal_hasDeriv μ K' L), HasFDerivAt.fderiv (x := (phiReal K' L x)) (by apply phiReal_hasDeriv μ K K')]
--     -- ext
--     unfold phiDerivReal
--     simp only [Rat.cast_natCast, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, smul_eq_mul, one_mul]
--     --rw [max_eq_right]
--     --apply aux_2 K K' L
--     by_cases hc : ⌈x⌉ < 0
--     · have hc' : ⌈(phiReal K' L x)⌉ < 0 := by
--         rw [phiReal_eq_self_of_le_zero]
--         exact hc
--         apply le_of_lt (lt_of_le_of_lt (Int.le_ceil x) _)
--         simp only [← Int.cast_zero (R := ℝ), Int.cast_lt, hc]
--       rw [max_eq_left (le_of_lt hc), max_eq_left (le_of_lt hc'), div_self, div_self, div_self, one_mul]
--       repeat sorry
--     · push_neg at hc
--       have hc' : 0 ≤ ⌈(phiReal K' L x)⌉ := by
--         apply Int.ceil_nonneg
--         rw [← phiReal_zero_eq_zero K' L]
--         apply (phiReal_StrictMono K' L).monotone
--         sorry
--       rw [max_eq_right hc, max_eq_right hc']
--       calc
--         _ = (Nat.card (G(L/K)_[⌈x⌉].map (AlgEquiv.restrictNormalHom K')) : ℝ) * (Nat.card G(L/K')_[⌈x⌉] : ℝ) / ((Nat.card G(K'/K)_[0] : ℝ) * (Nat.card G(L/K')_[0] : ℝ)) := by
--           rw [← mul_div_mul_comm]
--           congr
--           rw [herbrand_Real]
--         _ = _ := by
--           congr
--           apply RamificationGroup_card_comp_aux K K' L
--           apply RamificationGroup_card_zero_comp_aux K K'
--     apply Differentiable.differentiableAt (phiReal_Defferentiable K K')
--     apply Differentiable.differentiableAt (phiReal_Defferentiable K' L)



-- @[simp]
-- theorem phi_comp_of_isValExtension' (u : ℚ): (phi K K') ((phi K' L) u) = (phi K L) u := by
--   have : ((phi K K') ((phi K' L) u) : ℝ) = ((phi K L) u  : ℝ) := by
--     rw [← phiReal_eq_phi K L, ← phiReal_eq_phi K K', ← phiReal_eq_phi K' L, ← Function.comp_apply (f := phiReal K K')]
--     rw [phiReal_comp_of_isValExtension' K K' L]
--   apply_mod_cast this
