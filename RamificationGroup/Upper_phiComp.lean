import RamificationGroup.UpperNumbering
import Mathlib.Algebra.Order.Pointwise

open QuotientGroup IntermediateField DiscreteValuation Valued Valuation HerbrandFunction

variable (μ : MeasureTheory.Measure ℝ)
variable (K K' L : Type*) {ΓK : outParam Type*} [Field K] [Field K'] [Field L] [vK : Valued K ℤₘ₀] [vK' : Valued K' ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK.v] [IsDiscrete vK'.v] [IsDiscrete vL.v] [Algebra K L] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L] [IsValExtension K K'] [IsValExtension K' L] [IsValExtension K L] [Normal K K'] [Normal K L] [FiniteDimensional K L] [FiniteDimensional K K'] [FiniteDimensional K' L]

noncomputable def phiDerivReal (u : ℝ) : ℝ :=
  (Nat.card G(L/K)_[(max 0 ⌈u⌉)] : ℚ) / (Nat.card G(L/K)_[0] : ℚ)

noncomputable def phiReal (u : Real) : Real := intervalIntegral (phiDerivReal K L) 0 u μ

--theorem continuous_phiDerivReal_aux : Continuous (phiDerivReal (K := K) (L := L)) := by sorry

theorem phiReal_eq_phi {u : ℚ} : phiReal μ K L u = phi K L u := by sorry

theorem phiReal_zero_eq_zero : phiReal μ K L 0 = 0 := by sorry

#check intervalIntegral.differentiableOn_integral_of_continuous

theorem phiReal_hasFDeriv {x : ℝ} :HasFDerivAt (𝕜 := ℝ) (phiReal μ K L) (ContinuousLinearMap.smulRight (S := ℝ) 1 (phiDerivReal K L x)) x:= by
  apply hasFDerivAt_iff_hasDerivAt.2
  sorry

theorem phiReal_hasDeriv {x : ℝ} : HasDerivAt (phiReal μ K L) (phiDerivReal K L x) x := by
  apply hasDerivAt_iff_hasFDerivAt.2
  apply phiReal_hasFDeriv

theorem phiReal_Defferentiable : Differentiable ℝ (phiReal μ K L) := by
  dsimp [Differentiable, DifferentiableAt]
  intro x
  use (ContinuousLinearMap.smulRight (S := ℝ) 1 (phiDerivReal K L x))
  apply phiReal_hasFDeriv


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

noncomputable def aux_7 {G H : Type*} [Group G] [Group H] {N : Subgroup G} {f : G →* H} (h : Function.Surjective f) : N.map f ≃ N ⧸ (N ⊓ f.ker).subgroupOf N := by
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
#check AlgEquiv.map_smul
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
  have h1 : (ofInjectiveField (IsScalarTower.toAlgHom K K' L)) t = (ofInjectiveField (IsScalarTower.toAlgHom K K' L)).toAlgHom.toAlgebra.toRingHom t := rfl
  rw [h1]
  -- haveI range : Subalgebra K' L := {
  --   carrier := (IsScalarTower.toAlgHom K K' L).range
  --   mul_mem' := ?mul_mem'
  --   one_mem' := ?one_mem'
  --   add_mem' := ?add_mem'
  --   zero_mem' := ?zero_mem'
  --   algebraMap_mem' := ?algebraMap_mem'
  -- }
  have h2 : ((ofInjectiveField (IsScalarTower.toAlgHom K K' L)).toAlgHom.toAlgebra.toRingHom t) = algebraMap K' L t := by
    rw [← algebraMap]
    exact rfl
  simp only [toAlgHom_eq_coe, toRingHom_eq_coe, toAlgHom_toRingHom, h2, commutes]

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
  simp only [Algebra.algebraMap_eq_smul_one]
  -- have h3 : (1 : (IsScalarTower.toAlgHom K K' L).range) = (1 : L) := rfl
  haveI : Algebra K' (IsScalarTower.toAlgHom K K' L).range := by
    refine (ofInjectiveField (IsScalarTower.toAlgHom K K' L)).toAlgHom.toAlgebra
  have h4 : t • (1 : L) ∈ (IsScalarTower.toAlgHom K K' L).range := by
    simp only [mem_range, IsScalarTower.coe_toAlgHom']
    use t
    apply Algebra.algebraMap_eq_smul_one
  have h5 : (ofInjectiveField (IsScalarTower.toAlgHom K K' L)).symm ⟨t • (1 : L), h4⟩ = (ofInjectiveField (IsScalarTower.toAlgHom K K' L)).symm (t • (1 : (IsScalarTower.toAlgHom K K' L).range)) := by
    refine AlgEquiv.congr_arg ?_
    refine SetCoe.ext ?_
    simp only
    -- have : (↑(t • (1 : ((IsScalarTower.toAlgHom K K' L).range))) : L) = (t • ↑((1 : ((IsScalarTower.toAlgHom K K' L).range)) : L)) := by
    sorry
  have h6 : algebraMap K' _ t = (ofInjectiveField (IsScalarTower.toAlgHom K K' L)) t := by
    rw [h1, ← algebraMap]
    congr
    sorry
  rw [h5, ← Algebra.algebraMap_eq_smul_one, h6]
  exact symm_apply_apply (ofInjectiveField (IsScalarTower.toAlgHom K K' L)) t

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


theorem AlgEquiv.restrictNormal_ker_eq : (AlgEquiv.restrictNormalHom K').ker = (⊤ : Subgroup (L ≃ₐ[K'] L)).map (AlgEquiv.restrictScalarsHom K) := by sorry

theorem RamificationGroup_card_comp_aux {x : ℝ} : (Nat.card (Subgroup.map (AlgEquiv.restrictNormalHom K') G(L/K)_[⌈x⌉]) : ℝ) * (Nat.card G(L/K')_[⌈x⌉] : ℝ) = (Nat.card G(L/K)_[⌈x⌉] : ℝ) := by
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
    apply aux_7
    exact AlgEquiv.restrictNormalHom_surjective L
  haveI h3 : (G(L/K')_[⌈x⌉].map (AlgEquiv.restrictScalarsHom K)) = (G(L/K)_[⌈x⌉] ⊓ (AlgEquiv.restrictNormalHom K').ker) := by
    ext t
    constructor
    <;> intro ht
    · apply Subgroup.mem_inf.2
      constructor
      · sorry
      · apply (MonoidHom.mem_ker (AlgEquiv.restrictNormalHom K')).2
        obtain ⟨y, hy1, hy2⟩ := Subgroup.mem_map.1 ht
        rw [← hy2]
        apply AlgEquiv.restrictNormalHom_restrictScalarsHom
    · apply Subgroup.mem_map.2
      rw [Subgroup.mem_inf] at ht
      by_contra hc
      push_neg at hc
      sorry
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

--variable [IsScalarTower 𝒪[K] 𝒪[K'] 𝒪[L]]
theorem RamificationGroup_card_zero_comp_aux : (Nat.card G(K'/K)_[0] : ℝ) * (Nat.card G(L/K')_[0] : ℝ) = (Nat.card G(L/K)_[0] : ℝ) := by
  repeat rw [RamificationIdx_eq_card_of_inertia_group]
  norm_cast
  unfold LocalField.ramificationIdx LocalRing.ramificationIdx
  let e_K'K := Ideal.ramificationIdx (algebraMap ↥𝒪[K] ↥𝒪[K']) (LocalRing.maximalIdeal ↥𝒪[K]) (LocalRing.maximalIdeal ↥𝒪[K'])
  let e_LK' := Ideal.ramificationIdx (algebraMap ↥𝒪[K'] ↥𝒪[L]) (LocalRing.maximalIdeal ↥𝒪[K']) (LocalRing.maximalIdeal ↥𝒪[L])
  let e_LK := Ideal.ramificationIdx (algebraMap ↥𝒪[K] ↥𝒪[L]) (LocalRing.maximalIdeal ↥𝒪[K]) (LocalRing.maximalIdeal ↥𝒪[L])
  have h : (LocalRing.maximalIdeal 𝒪[L]) ^ (e_K'K * e_LK') = (LocalRing.maximalIdeal 𝒪[L]) ^ (e_LK) := by
    dsimp [e_K'K, e_LK', e_LK]
    haveI : IsScalarTower 𝒪[K] 𝒪[K'] 𝒪[L] := by sorry
    rw [← maximalIdeal_map_eq_maximalIdeal_pow_ramificationIdx (IsValExtension.integerAlgebra_injective K L), mul_comm, pow_mul, ← maximalIdeal_map_eq_maximalIdeal_pow_ramificationIdx (IsValExtension.integerAlgebra_injective K' L), ← Ideal.map_pow, ← maximalIdeal_map_eq_maximalIdeal_pow_ramificationIdx (IsValExtension.integerAlgebra_injective K K'), Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  sorry


theorem herbrand_Real (u : ℝ) : G(L/K)_[⌈u⌉].map (AlgEquiv.restrictNormalHom K') = G(K'/K)_[⌈phiReal μ K' L u⌉] := by sorry

#check eq_of_has_deriv_right_eq

theorem phiReal_comp_of_isValExtension {u : ℝ} : ((phiReal μ K K') ∘ (phiReal μ K' L)) u = phiReal μ K L u := by
  have hdf : ∀ x ∈ Set.Ico (⌊u⌋ : ℝ) (⌊u⌋ + 1 : ℝ), HasDerivWithinAt (phiReal μ K K' ∘ phiReal μ K' L) (phiDerivReal K L x) (Set.Ici x) x := by sorry
  have hdg : ∀ x ∈ Set.Ico (⌊u⌋ : ℝ) (⌊u⌋ + 1 : ℝ), HasDerivWithinAt (phiReal μ K L) (phiDerivReal K L x) (Set.Ici x) x := by sorry
  have hcf : ContinuousOn (phiReal μ K K' ∘ phiReal μ K' L) (Set.Icc (⌊u⌋) (⌊u⌋ + 1)) := by sorry
  have hcg : ContinuousOn (phiReal μ K L) (Set.Icc (⌊u⌋) (⌊u⌋ + 1)) := by sorry
  apply eq_of_has_deriv_right_eq hdf hdg hcf hcg
  sorry
  sorry



theorem phiReal_comp_of_isValExtension' : (phiReal μ K K') ∘ (phiReal μ K' L) = phiReal μ K L := by
  apply eq_of_fderiv_eq (𝕜 := ℝ) (x := 0)
  · rw [Function.comp_apply, phiReal_zero_eq_zero, phiReal_zero_eq_zero, phiReal_zero_eq_zero]
  · apply Differentiable.comp (phiReal_Defferentiable μ K K') (phiReal_Defferentiable μ K' L)
  · apply phiReal_Defferentiable
  · intro x
    conv =>
      right
      rw [HasFDerivAt.fderiv (x := x) (by apply phiReal_hasDeriv μ K L)]
    ext
    rw [fderiv_deriv, deriv.comp, HasDerivAt.deriv (x := x) (by apply phiReal_hasDeriv μ K' L), HasDerivAt.deriv (x := (phiReal μ K' L x)) (by apply phiReal_hasDeriv μ K K')]
    -- conv =>
    --   enter [1, 2]
    --   rw [HasDerivAt.deriv]
    -- rw [fderiv.comp, HasFDerivAt.fderiv (x := x) (by apply phiReal_hasDeriv μ K' L), HasFDerivAt.fderiv (x := (phiReal μ K' L x)) (by apply phiReal_hasDeriv μ K K')]
    -- ext
    unfold phiDerivReal
    simp only [Rat.cast_natCast, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, smul_eq_mul, one_mul]
    --rw [max_eq_right]
    --apply aux_2 K K' L
    by_cases hc : ⌈x⌉ < 0
    · have hc' : ⌈(phiReal μ K' L x)⌉ < 0 := by sorry
      rw [max_eq_left (le_of_lt hc), max_eq_left (le_of_lt hc'), div_self, div_self, div_self, one_mul]
      repeat sorry
    · push_neg at hc
      have hc' : 0 ≤ ⌈(phiReal μ K' L x)⌉ := by sorry
      rw [max_eq_right hc, max_eq_right hc']
      calc
        _ = (Nat.card (G(L/K)_[⌈x⌉].map (AlgEquiv.restrictNormalHom K')) : ℝ) * (Nat.card G(L/K')_[⌈x⌉] : ℝ) / ((Nat.card G(K'/K)_[0] : ℝ) * (Nat.card G(L/K')_[0] : ℝ)) := by
          rw [← mul_div_mul_comm]
          congr
          rw [herbrand_Real]
        _ = _ := by
          congr
          apply RamificationGroup_card_comp_aux K K' L
          apply RamificationGroup_card_zero_comp_aux K K'
    apply Differentiable.differentiableAt (phiReal_Defferentiable μ K K')
    apply Differentiable.differentiableAt (phiReal_Defferentiable μ K' L)



@[simp]
theorem phi_comp_of_isValExtension' (u : ℚ): (phi K K') ((phi K' L) u) = (phi K L) u := by
  have : ((phi K K') ((phi K' L) u) : ℝ) = ((phi K L) u  : ℝ) := by
    rw [← phiReal_eq_phi μ K L, ← phiReal_eq_phi μ K K', ← phiReal_eq_phi μ K' L, ← Function.comp_apply (f := phiReal μ K K')]
    rw [phiReal_comp_of_isValExtension' μ K K' L]
  apply_mod_cast this
