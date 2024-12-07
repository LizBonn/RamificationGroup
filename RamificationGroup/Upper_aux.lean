import RamificationGroup.Upper_phiComp

open QuotientGroup IntermediateField DiscreteValuation Valued Valuation HerbrandFunction
open MeasureTheory.MeasureSpace
open Pointwise
open AlgEquiv AlgHom
open LocalRing ExtDVR
open Asymptotics Filter intervalIntegral MeasureTheory

--variable (μ : MeasureTheory.Measure ℝ)
variable (K K' L : Type*) {ΓK : outParam Type*} [Field K] [Field K'] [Field L] [vK : Valued K ℤₘ₀] [vK' : Valued K' ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK.v] [IsDiscrete vK'.v] [IsDiscrete vL.v] [Algebra K L] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L] [IsValExtension K K'] [IsValExtension K' L] [IsValExtension K L] [Normal K K'] [Normal K L] [FiniteDimensional K L] [FiniteDimensional K K'] [FiniteDimensional K' L] [CompleteSpace K] [CompleteSpace K'] [Algebra.IsSeparable K' L] [Algebra.IsSeparable (LocalRing.ResidueField ↥𝒪[K']) (LocalRing.ResidueField ↥𝒪[L])]


set_option synthInstance.maxHeartbeats 100000
#check preimage_nhds_coinduced
#check Filter.map_eq_map_iff_of_injOn

theorem nhds_neg_aux {x : ℝ} {k : Set ℝ} (h : k ∈ nhds x) : -k ∈ nhds (-x) := by
  rw [mem_nhds_iff] at *
  obtain ⟨m, hm1, hm2, hm3⟩ := h
  use -m
  constructor
  · simp only [Set.neg_subset_neg, hm1]
  · constructor
    · exact IsOpen.neg hm2
    · exact Set.neg_mem_neg.mpr hm3

theorem Set.neg_Icc {a b : ℝ} : -(Set.Icc a b) = Set.Icc (-b) (-a) := by
  ext x
  simp only [preimage_neg_Icc, mem_Icc]

theorem Set.neg_Ici {a : ℝ} : Set.Ici a = - Set.Iic (-a) := by
  ext x
  simp only [mem_Ici, preimage_neg_Iic, neg_neg]

theorem Set.neg_Ioc {a b : ℝ} : Set.Ioc a b = - (Set.Ico (-b) (-a)) := by
  ext x
  simp only [mem_Ioc, preimage_neg_Ico, neg_neg]


theorem ContinuousOn_inv_aux {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : ℝ → E} {a b : ℝ} (hf : ∀x : ℝ, f x = g (-x)) (fcont : ContinuousOn f (Set.Icc a b)) : ContinuousOn g (Set.Icc (-b) (-a)) := by
  dsimp [ContinuousOn, ContinuousWithinAt, Tendsto]
  intro x hx
  have h' : g x = f (-x) := by rw [hf (-x), neg_neg]
  have h : Filter.map g (nhdsWithin x (Set.Icc (-b) (-a))) = Filter.map f (nhdsWithin (-x) (Set.Icc a b)) := by
    ext t
    constructor
    <;> intro ht
    · obtain ⟨k, hk1, hk2⟩ := ht
      use -k
      constructor
      · apply nhds_neg_aux hk1
      -- · rw [mem_nhds_iff] at *
      --   obtain ⟨m, hm1, hm2, hm3⟩ := hk1
      --   use -m
      --   constructor
      --   · simp only [Set.neg_subset_neg, hm1]
      --   · constructor
      --     · exact IsOpen.neg hm2
      --     · exact Set.neg_mem_neg.mpr hm3
      · obtain ⟨c, hc1, hc2⟩ := hk2
        use -c
        constructor
        · rw [mem_principal] at *
          have h'' : Set.Icc (-b) (-a) = -(Set.Icc a b) := by apply Eq.symm Set.neg_Icc
          rw [h''] at hc1
          exact Set.neg_subset.mp hc1
        · rw [Set.preimage] at *
          have h'' : {x | f x ∈ t} = -{x | g x ∈ t} := by
            ext k
            simp only [Set.mem_setOf_eq, Set.mem_neg]
            constructor
            <;> intro hk
            · rw [← hf k]
              exact hk
            · rw [hf k]
              exact hk
          have h''' : -k ∩ -c = - (k ∩ c) := by exact rfl
          rw [h'', h''']
          exact congrArg Neg.neg hc2
    · obtain ⟨k, hk1, hk2⟩ := ht
      use -k
      constructor
      · rw [← neg_neg x]
        apply nhds_neg_aux hk1
      -- · rw [mem_nhds_iff] at *
      --   obtain ⟨m, hm1, hm2, hm3⟩ := hk1
      --   use -m
      --   constructor
      --   · simp only [Set.neg_subset_neg, hm1]
      --   · constructor
      --     · exact IsOpen.neg hm2
      --     · exact hm3
      · obtain ⟨c, hc1, hc2⟩ := hk2
        use -c
        constructor
        · rw [mem_principal] at *
          have h'' : Set.Icc (-b) (-a) = -(Set.Icc a b) := by apply Eq.symm Set.neg_Icc
          rw [h'']
          simp only [Set.neg_subset_neg, hc1]
        · rw [Set.preimage] at *
          have h'' : -{x | f x ∈ t} = {x | g x ∈ t} := by
            ext k
            simp only [Set.mem_setOf_eq, Set.mem_neg]
            constructor
            <;> intro hk
            · rw [← neg_neg k, ← hf (-k)]
              exact hk
            · rw [hf (-k), neg_neg]
              exact hk
          have h''' : -k ∩ -c = - (k ∩ c) := by exact rfl
          rw [←h'', h''']
          exact congrArg Neg.neg hc2
  rw [h, h']
  apply fcont
  apply Set.mem_neg.1
  rw [Set.neg_Icc]
  apply hx
  --   unfold Filter.map
  --   simp only [Filter.mk.injEq]
  --   ext t
  --   constructor
  --   <;> intro ht
  --   · rw [Set.mem_preimage, Set.preimage]
  --     apply preimage_nhdsWithin_coinduced' ?_ ?_
  --     sorry
  --     obtain ⟨k, hk1, hk2⟩ := ht
  --     rw [← h']
  --     sorry
  --   · sorry
  -- rw [h', h, ← Tendsto]
  -- dsimp [ContinuousOn, ContinuousWithinAt] at fcont
  -- apply fcont (-x)
  -- rw [Set.mem_Icc] at *
  -- sorry

theorem HasDerivWithinAt_inv_aux {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E] {f finv f' finv' : ℝ → E} {a b : ℝ} (derivf : ∀ x ∈ Set.Ioc a b, HasDerivWithinAt f (f' x) (Set.Iic x) x) (h : ∀ x : ℝ, f x = finv (-x)) (h' : ∀ x : ℝ, f' x = - finv' (-x)) : ∀ x ∈ Set.Ico (-b) (-a), HasDerivWithinAt finv (finv' x) (Set.Ici x) x := by
  intro x hx
  dsimp [HasDerivWithinAt, HasDerivAtFilter]
  -- intro x hx
  -- have h : HasDerivWithinAt f (f' (-x)) (Set.Iic (-x)) (-x) := by
  --   apply derivf (-x)
  --   sorry

  -- dsimp [HasDerivWithinAt, HasDerivAtFilter] at *
  -- #check h.isLittleO
  haveI h : HasFDerivAtFilter (𝕜 := ℝ) finv (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (finv' x)) x (nhdsWithin x (Set.Ici x)) := {
    isLittleO := by
      rw [IsLittleO_def]
      intro c hc
      rw [IsBigOWith_def]
      obtain ⟨k, hk1, hk2⟩ := isLittleO_iff.1 (derivf (-x) ?_).isLittleO hc
      use -k
      constructor
      · rw [← neg_neg x]
        apply nhds_neg_aux hk1
      · obtain ⟨t, ht1, ht2⟩ := hk2
        use -t
        constructor
        · rw [mem_principal] at *
          have h' : Set.Ici x = - (Set.Iic (-x)) := by apply Set.neg_Ici
          rw [h', Set.neg_subset_neg]
          exact ht1
        · rw [← Set.inter_neg, ← ht2]
          ext t
          simp only [_root_.map_sub, ContinuousLinearMap.smulRight_apply,
            ContinuousLinearMap.one_apply, Real.norm_eq_abs, Set.mem_setOf_eq, sub_neg_eq_add,
            _root_.map_add, Set.mem_neg, neg_smul, h (-t), h (-x), h' (-x), neg_neg]
          simp only [smul_neg, neg_neg, ← sub_eq_add_neg]
          rw [← abs_neg, neg_sub, neg_add_eq_sub]
      -- have h1 : ∀ x : ℝ, finv x = f (-x) := by sorry
      -- have h2 : ∀ x : ℝ, finv' x = -f' (-x) := by sorry
      -- have h2 : (fun x' ↦ finv x' - finv x - (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (finv' x)) (x' - x)) = (fun x' ↦ f (-x') - f (-x) - (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-f' (-x))) (x' - x)) := by
      --   ext x'
      --   rw [h1 x', h1 x, h2 x]
      -- have h3 : (fun x' ↦ f x' - f (-x) - (ContinuousLinearMap.smulRight 1 (f' (-x))) (x' - -x)) =o[nhdsWithin (-x) (Set.Iic (-x))] fun x' ↦ x' - -x := h.isLittleO
      -- rw [h2, isLittleO_iff]
      -- rw [isLittleO_iff] at h3
      -- intro c hc
      -- obtain ⟨t, ht⟩ := h3 hc
  }
  rw [Set.neg_Ioc, Set.mem_neg, neg_neg]
  exact hx
  exact h

theorem eq_of_has_deriv_left_eq {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {a b : ℝ} {f' g : ℝ → E} (derivf : ∀ x ∈ Set.Ioc a b, HasDerivWithinAt f (f' x) (Set.Iic x) x) (derivg : ∀ x ∈ Set.Ioc a b, HasDerivWithinAt g (f' x) (Set.Iic x) x) (fcont : ContinuousOn f (Set.Icc a b)) (gcont : ContinuousOn g (Set.Icc a b)) (hi : f b = g b) (y : ℝ) : y ∈ Set.Icc a b → f y = g y := by
  let finv : ℝ → E := fun x => f (-x)
  let ginv : ℝ → E := fun x => g (-x)
  let finv' : ℝ → E := fun x => - f' (-x)
  have h : ∀x : ℝ, x ∈ Set.Icc (-b) (-a) → finv x = ginv x := by
    apply eq_of_has_deriv_right_eq (f' := finv')
    · apply HasDerivWithinAt_inv_aux derivf
      · intro x
        dsimp [finv]
        simp only [neg_neg]
      · intro x
        dsimp [finv']
        simp only [neg_neg]
    · apply HasDerivWithinAt_inv_aux derivg
      · intro x
        dsimp [ginv]
        simp only [neg_neg]
      · intro x
        dsimp [finv']
        simp only [neg_neg]
    · apply ContinuousOn_inv_aux (f := f) (g := finv) _ fcont
      intro x
      dsimp [finv]
      simp only [neg_neg]
    · apply ContinuousOn_inv_aux (f := g) (g := ginv) _ gcont
      intro x
      dsimp [ginv]
      simp only [neg_neg]
    · dsimp [finv, ginv]
      simp only [neg_neg, hi]
  intro hy
  have h' : finv (-y) = ginv (-y) := by
    apply h
    simp only [Set.mem_Icc, neg_le_neg_iff, And.comm]
    rw [← Set.mem_Icc (α := ℝ) (a := a) (b := b) (x := y)]
    exact hy
  dsimp [finv, ginv] at h'
  simp only [neg_neg] at h'
  exact h'

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


theorem phiReal_StrictMono_aux : StrictMono (phiReal K L) := by
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

theorem phiReal_comp_of_isValExtension_neg_aux {u : ℝ} (hu : u < 0) : ((phiReal K K') ∘ (phiReal K' L)) u = phiReal K L u := by
  rw [Function.comp_apply, phiReal_eq_self_of_le_zero K L (le_of_lt hu), phiReal_eq_self_of_le_zero K' L (le_of_lt hu), phiReal_eq_self_of_le_zero K K' (le_of_lt hu)]

theorem phiDerivReal_le_one {u : ℝ} (h : 0 < u) : phiDerivReal K L u ≤ 1 := by
  have h' : 0 ≤ ⌈u⌉ := le_of_lt (Int.ceil_pos.2 h)
  rw [phiDerivReal, max_eq_right, div_le_one, Nat.cast_le]
  apply Nat.card_mono
  exact Set.toFinite (G(L/K)_[0] : Set (L ≃ₐ[K] L))
  apply lowerRamificationGroup.antitone
  exact h'
  simp only [Nat.cast_pos, Nat.card_pos]
  exact h'


noncomputable def phiDerivReal' (u : ℝ) : ℝ := (Nat.card G(L/K)_[(⌊u⌋ + 1)] : ℝ) / (Nat.card G(L/K)_[0])

theorem phiDerivReal'_antitone : Antitone (phiDerivReal' K L) := by
  intro x y hxy
  unfold phiDerivReal'
  apply (div_le_div_right _).2
  apply Nat.mono_cast
  apply Nat.card_mono
  exact Set.toFinite  (G(L/K)_[(⌊x⌋ + 1)] : Set (L ≃ₐ[K] L))
  apply lowerRamificationGroup.antitone
  linarith [Int.floor_le_floor (α := ℝ) x y hxy]
  simp only [Nat.cast_pos, Nat.card_pos]

-- theorem phiDerivReal'_phiDerivReal {u : ℝ} : phiDerivReal' K L u = phiDerivReal K L (u + ⌈u⌉ - ⌊u⌋) := by sorry


theorem phiDerivReal'_eq_phiDerivReal_mul_of {u : ℝ} (h : u = ⌈u⌉) (h' : 0 < u) : phiDerivReal' K L u = phiDerivReal K L u * ((Nat.card G(L/K)_[(⌈u⌉ + 1)] : ℝ) / (Nat.card G(L/K)_[⌈u⌉] : ℝ)) := by
  rw [phiDerivReal', phiDerivReal, max_eq_right, ← mul_div_mul_comm, mul_comm, mul_div_mul_comm, div_self, mul_one, h, Int.floor_intCast, Int.ceil_intCast]
  apply ne_of_gt
  simp only [Nat.cast_pos, Nat.card_pos]
  apply Int.ceil_nonneg (le_of_lt h')

theorem phiDerivReal'_eq_phiDerivReal_add_one_of {u : ℝ} (h : u = ⌈u⌉) (h' : 0 < u) : phiDerivReal' K L u = phiDerivReal K L (u + 1) := by
  rw [phiDerivReal', phiDerivReal, max_eq_right, h, Int.floor_intCast, Int.ceil_add_one, Int.ceil_intCast]
  apply Int.ceil_nonneg
  apply le_of_lt (lt_trans h' (by linarith))

theorem phiDerivReal'_eq_phiDerivReal_of {u : ℝ} (h : u ≠ ⌈u⌉) (h' : 0 < u) : phiDerivReal' K L u = phiDerivReal K L u := by
  unfold phiDerivReal' phiDerivReal
  rw [max_eq_right (le_of_lt (Int.ceil_pos.2 h'))]
  have h1 : ⌈u⌉ = ⌊u⌋ + 1 := by
    symm
    apply le_antisymm _ (Int.ceil_le_floor_add_one u)
    apply Int.add_one_le_of_lt
    apply lt_of_le_of_ne (Int.floor_le_ceil u)
    by_contra hc
    apply h
    apply le_antisymm
    exact Int.le_ceil u
    rw [← hc]
    exact Int.floor_le u
  rw [h1]


#check RamificationGroup_card_comp_aux
#check RamificationGroup_card_zero_comp_aux

variable [IsScalarTower 𝒪[K] 𝒪[K'] 𝒪[L]]

theorem phiDerivReal'_comp_zero : (phiDerivReal' K' L 0) * (phiDerivReal' K K' (phiReal K' L 0)) = phiDerivReal' K L 0 := by
  unfold phiDerivReal'
  simp only [phiReal_zero_eq_zero, Int.floor_zero, zero_add, ← mul_div_mul_comm]
  congr
  rw [← Int.ceil_one (α := ℝ), ← RamificationGroup_card_comp_aux K K' L, mul_comm, mul_eq_mul_right_iff]
  left
  have hp : ⌈phiReal K' L 1⌉ = 1 := by
    apply Int.ceil_eq_iff.2
    simp only [Int.cast_one, sub_self]
    constructor
    · rw [← phiReal_zero_eq_zero K' L]
      apply phiReal_StrictMono K' L (by linarith)
    · apply phiReal_one_le_one K' L
  rw [Nat.cast_inj, Nat.card_congr, herbrand_Real, hp]
  simp only [Int.ceil_one]
  exact Equiv.setCongr rfl
  rw[mul_comm, RamificationGroup_card_zero_comp_aux K K' L]

theorem phiDerivReal'_comp {u : ℝ} (h : 0 < u) : (phiDerivReal' K' L u) * phiDerivReal' K K' (phiReal K' L u) = phiDerivReal' K L u := by
  have h' : ∃ v : ℝ, ⌈v⌉ = ⌊u⌋ + 1 ∧ ⌈phiReal K' L v⌉ = ⌊phiReal K' L u⌋ + 1 := by
    have h'' : ∃ v : ℝ, v ∈ Set.Ioc u (⌊u⌋ + 1) ∧ v ∈ Set.Ioc u (u + ⌊phiReal K' L u⌋ + 1 - phiReal K' L u) := by
      simp only [← Set.mem_inter_iff, ← Set.nonempty_def, Set.Ioc_inter_Ioc, le_refl, sup_of_le_left, Set.nonempty_Ioc, lt_inf_iff, Int.lt_floor_add_one, true_and, add_assoc, add_sub_assoc, lt_add_iff_pos_right]
      rw [add_sub_assoc', sub_pos]
      exact Int.lt_floor_add_one (phiReal K' L u)
    obtain ⟨v, hv1, hv2⟩ := h''
    use v
    constructor
    · apply Int.ceil_eq_iff.2
      constructor
      · simp only [Int.cast_add, Int.cast_one, add_sub_cancel_right]
        apply lt_of_le_of_lt (Int.floor_le u) (Set.mem_Ioc.1 hv1).1
      · apply_mod_cast (Set.mem_Ioc.1 hv1).2
    · apply Int.ceil_eq_iff.2
      constructor
      · simp only [Int.cast_add, Int.cast_one, add_sub_cancel_right]
        apply lt_of_le_of_lt (Int.floor_le (phiReal K' L u))
        apply phiReal_StrictMono K' L (Set.mem_Ioc.1 hv1).1
      · rw [← add_le_add_iff_right (-phiReal K' L u), ← sub_eq_add_neg]
        calc
            _ ≤ (v - u) * phiDerivReal K' L u := by
              apply phiReal_sub_phiReal_le K' L (le_of_lt (Set.mem_Ioc.1 hv1).1) h
            _ ≤ v - u := by
              nth_rw 2 [← mul_one (v - u)]
              rw [mul_le_mul_left]
              apply phiDerivReal_le_one K' L h
              apply lt_add_neg_iff_lt.2 (Set.mem_Ioc.1 hv1).1
            _ ≤ _ := by
              rw [← sub_eq_add_neg, tsub_le_iff_left]
              convert (Set.mem_Ioc.1 hv2).2 using 1
              simp only [Int.cast_add, Int.cast_one, add_assoc, add_sub_assoc]
  obtain ⟨v, hv1, hv2⟩ := h'
  obtain hcm := phiDerivReal_comp K K' L (u := v)
  unfold phiDerivReal at hcm
  rw [max_eq_right, max_eq_right] at hcm
  unfold phiDerivReal'
  rw [← hv1, ← hv2, hcm]
  · rw [hv2]
    have h' : 0 ≤ ⌊phiReal K' L u⌋ := by
      apply Int.floor_nonneg.2 (le_of_lt (phiReal_pos_of_pos K' L h))
    exact Int.le_add_one h'
  · rw [hv1]
    have h' : 0 ≤ ⌊u⌋ := Int.floor_nonneg.2 (le_of_lt h)
    exact Int.le_add_one h'
    -- by_cases hc : u = ⌈u⌉
    -- · by_cases hc' : phiReal K' L u = ⌈phiReal K' L u⌉
    --   · obtain ⟨v, hv1, hv2⟩ := h'
    --     rw [phiDerivReal'_eq_phiDerivReal_add_one_of K L hc h, phiDerivReal'_eq_phiDerivReal_add_one_of K' L hc h, phiDerivReal'_eq_phiDerivReal_add_one_of K K']
    --     unfold phiDerivReal


  -- by_cases hc : u = ⌈u⌉
  -- · by_cases hc' : phiReal K' L u = ⌈phiReal K' L u⌉
  --   · rw [phiDerivReal'_eq_phiDerivReal_mul_of K L hc, phiDerivReal'_eq_phiDerivReal_mul_of K' L hc, phiDerivReal'_eq_phiDerivReal_mul_of K K' hc']
  --   · sorry
  -- · by_cases hc' : phiReal K' L u = ⌈phiReal K' L u⌉
  --   · sorry
  --   · sorry


  -- · rw [← Int.ceil_intCast (α := ℝ), ← RamificationGroup_card_comp_aux K K' L, mul_comm]
  --   congr 1
  --   rw [max_eq_right, ← herbrand_Real, max_eq_right]
  --   simp only [Subgroup.mem_map, Int.ceil_intCast]
  --   sorry
  --   sorry
  -- · rw [← Int.ceil_zero (α := ℝ), ← RamificationGroup_card_comp_aux K K' L, mul_comm]
  --   congr 1
  --   rw [herbrand_Real, phiReal_zero_eq_zero]

-- theorem phiDerivReal'_sub_phiDerivReal'_le {u v : ℝ} (h : u ≤ v) : phiDerivReal' K L u - phiDerivReal' K L v ≤ v - u := by
--   unfold phiDerivReal'

--   sorry

#check Int.ceil_eq_add_one_sub_fract
#check Int.fract
theorem phiReal_eq_sum_card' {u : ℝ} (hu : 0 < u) : phiReal K L u = (1 / Nat.card G(L/K)_[0]) * ((∑ x in Finset.Icc 1 ⌊u⌋, Nat.card G(L/K)_[x]) + (u - (max 0 ⌊u⌋)) * (Nat.card G(L/K)_[(⌊u⌋ + 1)])) := by
  rw [phiReal_eq_sum_card K L (le_of_lt hu), mul_eq_mul_left_iff]
  left
  by_cases hc : ⌈u⌉ - 1 = ⌊u⌋
  · simp only [hc, Int.cast_max, Int.cast_zero, add_comm ⌊u⌋, ← (eq_add_of_sub_eq' hc)]
  · have h2 : ⌊u⌋ = u := by
      by_contra hcon
      apply hc
      rw [← Int.cast_inj (α := ℝ), Int.cast_sub, Int.ceil_eq_add_one_sub_fract, Int.fract]
      ring
      unfold Int.fract
      exact sub_ne_zero_of_ne fun a ↦ hcon (id (Eq.symm a))
    have h1 : ⌈u⌉ = u := by rw [← h2, Int.ceil_intCast]
    have h3 : ⌈u⌉ = ⌊u⌋ := by rw [← Int.cast_inj (α := ℝ), h1, h2]
    have h' : Finset.Icc 1 ⌊u⌋ = Finset.Icc 1 (⌊u⌋ - 1) ∪ {⌊u⌋} := by
      ext x
      constructor
      <;>intro hx
      · apply Finset.mem_union.2
        by_cases hx' : x ≤ ⌊u⌋ - 1
        · left
          apply Finset.mem_Icc.2
          refine ⟨(Finset.mem_Icc.1 hx).1, hx'⟩
        · right
          simp only [Finset.mem_singleton]
          apply eq_of_le_of_not_lt (Finset.mem_Icc.1 hx).2
          push_neg at *
          rw [← sub_add_cancel ⌊u⌋ 1]
          apply (Int.add_one_le_iff (a := ⌊u⌋ - 1) (b := x)).2 hx'
      · rw [Finset.mem_union] at hx
        match hx with
        | Or.inl hx =>
                      apply Finset.mem_Icc.2
                      refine ⟨(Finset.mem_Icc.1 hx).1, le_trans (Finset.mem_Icc.1 hx).2 (by linarith)⟩
        | Or.inr hx =>
                      rw [Finset.mem_singleton] at hx
                      rw [hx]
                      apply Finset.right_mem_Icc.2
                      rw [← h3]
                      apply (Int.add_one_le_iff (a := 0) (b := ⌈u⌉)).2 (Int.ceil_pos.2 hu)
    rw [h3, ← sub_eq_zero, ← sub_sub, add_sub_right_comm, max_eq_right, max_eq_right, add_sub_assoc, Int.cast_sub, h2, Nat.cast_sum, Int.cast_one, sub_sub_cancel, one_mul, sub_self, zero_mul, sub_zero, sub_add_comm, sub_add, sub_eq_zero, h', Finset.sum_union, Nat.cast_add, Nat.cast_sum, add_sub_cancel_left, Finset.sum_singleton]
    simp only [Finset.disjoint_singleton_right, Finset.mem_Icc, le_sub_self_iff, Int.reduceLE, and_false, not_false_eq_true]
    exact Int.floor_nonneg.2 (le_of_lt hu)
    rw [← h3]
    apply Int.le_sub_one_iff.2 (Int.ceil_pos.2 hu)

theorem phiReal_sub_phiReal_le' {u v : ℝ} (h : u ≤ v) (h': 0 < u) : phiReal K L v - phiReal K L u ≤ (v - u) * phiDerivReal' K L u := by
  by_cases hc : u ≠ ⌈u⌉
  · rw [phiDerivReal'_eq_phiDerivReal_of K L hc h']
    apply phiReal_sub_phiReal_le K L h h'
  · push_neg at hc
    have h1 : Finset.Icc 1 ⌊v⌋ = Finset.Icc 1 ⌊u⌋ ∪ Finset.Icc (⌊u⌋ + 1) ⌊v⌋ := by
      ext x
      simp only [Finset.mem_union, Finset.mem_Icc]
      constructor
      <;> intro hx
      · by_cases hc : x ≤ ⌊u⌋
        · left
          refine ⟨hx.1, hc⟩
        · right
          constructor
          · push_neg at hc
            apply Int.le_of_sub_one_lt
            rw [add_sub_cancel_right]
            exact hc
          · exact hx.2
      · match hx with
        | Or.inl hx => refine ⟨hx.1, le_trans hx.2 (Int.floor_le_floor u v h)⟩
        | Or.inr hx => refine ⟨le_trans ?_ hx.1, hx.2⟩
                       simp only [le_add_iff_nonneg_left]
                       apply Int.floor_nonneg.2 (le_of_lt h')
    rw [phiReal_eq_sum_card' K L h', phiReal_eq_sum_card', phiDerivReal', ← mul_sub, one_div_mul_eq_div, ← mul_div_assoc, div_le_div_right, ← sub_sub, add_sub_right_comm, add_sub_assoc, h1, Finset.sum_union, Nat.cast_add, add_sub_cancel_left, max_eq_right, max_eq_right]
    calc
      _ ≤ ∑ x ∈ Finset.Icc (⌊u⌋ + 1) ⌊v⌋, Nat.card G(L/K)_[(⌊u⌋ + 1)] + ((v - ↑⌊v⌋) * ↑(Nat.card ↥ G(L/K)_[(⌊v⌋ + 1)] ) - (u - ↑⌊u⌋) * ↑(Nat.card ↥ G(L/K)_[(⌊u⌋ + 1)])) := by
        simp only [Int.cast_sub, Int.cast_one, add_le_add_iff_right, Nat.cast_le]
        apply Finset.sum_le_sum
        intro i hi
        apply Nat.card_mono
        exact Set.toFinite (G(L/K)_[(⌊u⌋ + 1)] : Set (L ≃ₐ[K] L))
        apply lowerRamificationGroup.antitone K L (Finset.mem_Icc.1 hi).1
      _ ≤  ∑ x ∈ Finset.Icc (⌊u⌋ + 1) ⌊v⌋, Nat.card G(L/K)_[(⌊u⌋ + 1)] + ((v - ↑⌊v⌋) * ↑(Nat.card ↥ G(L/K)_[(⌊u⌋ + 1)] ) - (u - ↑⌊u⌋) * ↑(Nat.card ↥ G(L/K)_[(⌊u⌋ + 1)])) := by
        simp only [add_le_add_iff_left, sub_eq_add_neg (b := (u - ↑⌊u⌋) * ↑(Nat.card ↥ G(L/K)_[(⌊u⌋ + 1)])), add_le_add_iff_right]
        by_cases hc : ⌊v⌋ = v
        · simp only [hc, sub_self, zero_mul, le_refl]
        · rw [mul_le_mul_left, Nat.cast_le]
          apply Nat.card_mono
          exact Set.toFinite (G(L/K)_[(⌊u⌋ + 1)] : Set (L ≃ₐ[K] L))
          apply lowerRamificationGroup.antitone K L
          linarith [Int.floor_le_floor u v h]
          rw [sub_pos]
          exact lt_of_le_of_ne (Int.floor_le v) hc
      _ ≤ _ := by
        simp only [Finset.sum_const, Int.card_Icc, sub_add_cancel, smul_eq_mul, Nat.cast_mul]
        rw [← Int.cast_natCast, Int.toNat_of_nonneg, ← sub_mul, ← add_mul, Int.cast_sub]
        have h1 : (↑(⌊v⌋ + 1) - ↑(⌊u⌋ + 1) + (v - ↑⌊v⌋ - (u - ↑⌊u⌋))) = v - u := by
          simp only [Int.cast_add, Int.cast_one]
          ring
        by_cases hc : u = v
        · simp only [hc, Int.cast_add, Int.cast_one, sub_self, Int.self_sub_floor, add_zero, zero_mul, le_refl]
        · rw [h1, mul_le_mul_left]
          rw [sub_pos]
          apply lt_of_le_of_ne h hc
        simp only [add_sub_add_right_eq_sub, sub_nonneg]
        apply Int.floor_le_floor u v h
    exact Int.floor_nonneg.2 (le_of_lt h')
    exact Int.floor_nonneg.2 (le_of_lt (lt_of_lt_of_le h' h))
    have h1 : Finset.Icc 1 ⌊u⌋ = Finset.Ico 1 (⌊u⌋ + 1) := rfl
    have h2 : Finset.Icc (⌊u⌋ + 1) ⌊v⌋ = Finset.Ico (⌊u⌋ + 1) (⌊v⌋ + 1) := rfl
    rw [h1, h2]
    apply Finset.Ico_disjoint_Ico_consecutive
    simp only [Nat.cast_pos, Nat.card_pos]
    apply lt_of_lt_of_le h' h

  -- rw [phiReal_eq_sum_card, phiReal_eq_sum_card]
  -- -- have h1 : (∑ x ∈ Finset.Icc 1 (⌈v⌉ - 1), Nat.card ↥ G(L/K)_[x]) - (∑ x ∈ Finset.Icc 1 (⌈u⌉ - 1), Nat.card ↥ G(L/K)_[x]) ≤ ∑ x ∈ Finset.Icc ⌈u⌉ (⌈v⌉ - 1), Nat.card G(L/K)_[⌈u⌉] := by sorry
  -- calc
  --   _ ≤  1 / (Nat.card G(L/K)_[0] ) * (∑ x ∈ Finset.Icc ⌈u⌉ (⌈v⌉ - 1), Nat.card G(L/K)_[⌈u⌉] + (v - (max 0 (⌈v⌉ - 1))) * (Nat.card G(L/K)_[⌈v⌉]) - (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈u⌉])) := by
  --     have h : Finset.Icc 1 (⌈v⌉ - 1) = Finset.Icc 1 (⌈u⌉ - 1) ∪ Finset.Icc ⌈u⌉ (⌈v⌉ - 1) := by sorry
  --     rw [h, Finset.sum_union, ← mul_sub, add_comm, ← sub_sub]
  --     rw [add_comm (∑ x ∈ Finset.Icc 1 (⌈u⌉ - 1), Nat.card ↥ G(L/K)_[x]), Nat.cast_add, ← add_assoc, mul_le_mul_left, add_sub_cancel_right, add_comm, ← add_sub, ← add_sub, add_le_add_iff_right, Nat.cast_le]
  --     apply Finset.sum_le_sum
  --     sorry
  --     sorry
  --     sorry
  --   _ =  1 / (Nat.card G(L/K)_[0] ) * ((⌈v⌉ - ⌈u⌉) * Nat.card G(L/K)_[⌈u⌉] + (v - (max 0 (⌈v⌉ - 1))) * (Nat.card G(L/K)_[⌈v⌉]) - (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈u⌉])) := by
  --     congr
  --     simp only [Finset.sum_const, Int.card_Icc, sub_add_cancel, smul_eq_mul, Nat.cast_mul, mul_eq_mul_right_iff, Nat.cast_eq_zero]
  --     left
  --     norm_cast
  --     rw [Int.toNat_of_nonneg]
  --     sorry
  --   _ ≤ _ := by
  --     sorry
  -- sorry
  -- sorry

theorem le_phiReal_sub_phiReal' {u v : ℝ} (h : u ≤ v) (h' : 0 < u) : (v - u) * phiDerivReal' K L v ≤ phiReal K L v - phiReal K L u := by
  by_cases hc : v ≠ ⌈v⌉
  · rw [phiDerivReal'_eq_phiDerivReal_of K L hc]
    apply le_phiReal_sub_phiReal K L h h'
    apply lt_of_lt_of_le h' h
  · push_neg at hc
    rw [phiDerivReal'_eq_phiDerivReal_mul_of K L hc]
    calc
      _ ≤  (v - u) * (phiDerivReal K L v) := by
        by_cases hc : u < v
        · rw [← mul_one ((v - u) * (phiDerivReal K L v)), ← mul_assoc, mul_le_mul_left, div_le_one ,Nat.cast_le]
          apply Nat.card_mono
          exact Set.toFinite (G(L/K)_[⌈v⌉] : Set (L ≃ₐ[K] L))
          apply lowerRamificationGroup.antitone
          linarith
          simp only [Nat.cast_pos, Nat.card_pos]
          apply mul_pos (by linarith [hc])
          apply phiDerivReal_pos K L
        · have heq : u = v := eq_of_le_of_not_lt h hc
          simp only [heq, sub_self, zero_mul, le_refl]
      _ ≤ _ := by
        apply le_phiReal_sub_phiReal K L h h'
    apply lt_of_lt_of_le h' h
  -- rw [phiReal_eq_sum_card, phiReal_eq_sum_card]
  -- calc
  --   _ ≤ 1 / (Nat.card G(L/K)_[0] ) * ((⌈v⌉ - 1 - ⌈u⌉) * Nat.card G(L/K)_[⌈v⌉] + (v - (max 0 (⌈v⌉ - 1))) * (Nat.card G(L/K)_[⌈v⌉]) - (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈v⌉])) := by sorry
  --   _ ≤ 1 / (Nat.card G(L/K)_[0] ) * (∑ x ∈ Finset.Icc ⌈u⌉ (⌈v⌉ - 1), Nat.card G(L/K)_[⌈v⌉] + (v - (max 0 (⌈v⌉ - 1))) * (Nat.card G(L/K)_[⌈v⌉]) - (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈u⌉])) := by sorry
  --   _ ≤ _ := by sorry
  -- sorry
  -- sorry

-- theorem phiReal_HasDerivWithinAt_section {n : ℕ} {u : ℝ} (h' : u ∈ Set.Ico (n : ℝ) (n + 1 : ℝ)) : HasDerivWithinAt (phiReal K L) (phiDerivReal' K L u) (Set.Ici u) u := by
--   unfold HasDerivWithinAt HasDerivAtFilter
--   haveI h : HasFDerivAtFilter (phiReal K L) (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (phiDerivReal' K L u)) u (nhdsWithin u (Set.Ici u)) := {
--     isLittleO := by
--       dsimp
--       rw [IsLittleO_def]
--       intro c hc
--       rw [IsBigOWith_def, eventually_iff]
--       refine mem_nhdsWithin_Ici_iff_exists_Ico_subset.mpr ?_
--       use min (u + c) (n + 1)
--       constructor
--       · apply Set.mem_Iio.2
--         rw [Set.mem_Ico] at h'
--         apply lt_min_iff.2
--         constructor
--         · linarith [hc]
--         · exact h'.2
--       · rw [Set.subset_def]
--         have h2 : ⌊u⌋ = n := by
--           apply Int.floor_eq_iff.2
--           simp only [Int.cast_natCast]
--           constructor
--           · apply (Set.mem_Ico.1 h').1
--           · apply (Set.mem_Ico.1 h').2
--         intro y hy
--         have h4 : ⌊u⌋ = ⌊y⌋ := by
--           rw [h2]
--           symm
--           apply Int.floor_eq_iff.2
--           simp only [Int.cast_natCast]
--           constructor
--           · apply le_trans (Set.mem_Ico.1 h').1 (Set.mem_Ico.1 hy).1
--           · exact (lt_min_iff.1 (Set.mem_Ico.1 hy).2).2
--         dsimp
--         by_cases hcase : n < u
--         · have hcase' : n < y := by
--             apply lt_of_lt_of_le hcase (Set.mem_Ico.1 hy).1
--           have h1 : ⌈u⌉ = n + 1 := by
--             apply Int.ceil_eq_iff.2
--             simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, add_sub_cancel_right]
--             constructor
--             · exact hcase
--             · exact le_of_lt (Set.mem_Ico.1 h').2
--           have h3 : ⌈u⌉ = ⌈y⌉ := by
--             rw [h1]
--             symm
--             apply Int.ceil_eq_iff.2
--             simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, add_sub_cancel_right]
--             constructor
--             · exact hcase'
--             · exact le_of_lt (lt_min_iff.1 (Set.mem_Ico.1 hy).2).2
--           have h5 : ⌈y⌉ = ⌊y⌋ + 1 := by
--             rw [← h3, h1, ← h4, h2]
--           rw [phiReal_eq_sum_card K L, phiReal_eq_sum_card K L, h3, phiDerivReal']
--           ring_nf
--           simp only [mul_comm (b := u), ← div_eq_inv_mul, mul_comm_div, add_sub, ← sub_eq_add_neg, ← mul_sub, mul_assoc, add_comm_sub, h4, h5, add_comm 1 ⌊y⌋, sub_self, mul_zero, add_zero, abs_zero]
--           apply mul_nonneg (le_of_lt hc) (abs_nonneg (y - u))
--           apply lt_of_le_of_lt (Nat.cast_nonneg n) hcase
--           apply lt_of_le_of_lt (Nat.cast_nonneg n) hcase'
--         · push_neg at hcase
--           have hcase' : u = n := by
--             apply le_antisymm hcase
--             apply le_trans _ (Set.mem_Ico.1 h').1
--             simp only [le_refl]
--           by_cases hcase'' : y = n
--           · simp only [hcase', hcase'', sub_self, zero_mul, abs_zero, mul_zero, le_refl]
--           · calc
--             _ ≤ |(y - u) * (phiDerivReal' K L u - phiDerivReal' K L y)| := by
--               simp only [← abs_neg (phiReal K L y - phiReal K L u - (y - u) * phiDerivReal' K L u), neg_sub]
--               apply abs_le_abs_of_nonneg
--               · simp only [sub_nonneg]
--                 apply phiReal_sub_phiReal_le' K L (Set.mem_Ico.1 hy).1
--               · simp only [mul_sub, sub_eq_add_neg ((y - u) * phiDerivReal' K L u), add_le_add_iff_left, neg_le_neg_iff]
--                 apply le_phiReal_sub_phiReal' K L (Set.mem_Ico.1 hy).1
--             _ ≤ _ := by
--               simp only [abs_mul]
--               rw [mul_comm, mul_le_mul_right]
--               apply le_trans (b := |y - u|)
--               apply abs_le_abs_of_nonneg
--               linarith [phiDerivReal'_antitone K L (Set.mem_Ico.1 hy).1]
--               unfold phiDerivReal'
--               rw [h4]
--               simp only [sub_self, sub_nonneg, ge_iff_le]
--               apply (Set.mem_Ico.1 hy).1
--               apply abs_le.2
--               constructor
--               · apply le_of_lt (lt_of_lt_of_le (b := 0) _ _)
--                 linarith [hc]
--                 linarith [(Set.mem_Ico.1 hy).1]
--               · linarith [(lt_min_iff.1 (Set.mem_Ico.1 hy).2).1]
--               apply abs_pos.2
--               rw [hcase', sub_ne_zero]
--               exact hcase''
--   }
--   exact h

-- theorem phiReal_comp_HasDerivWithinAt_section {n : ℕ} {u : ℝ} (h' : u ∈ Set.Ico (n : ℝ) (n + 1 : ℝ)) : HasDerivWithinAt (phiReal K K' ∘ phiReal K' L) (phiDerivReal' K L u) (Set.Ici u) u := by
--   unfold HasDerivWithinAt HasDerivAtFilter
--   haveI h : HasFDerivAtFilter (phiReal K K' ∘ phiReal K' L) (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (phiDerivReal' K L u)) u (nhdsWithin u (Set.Ici u)) := {
--     isLittleO := by
--       dsimp
--       rw [IsLittleO_def]
--       intro c hc
--       rw [IsBigOWith_def, eventually_iff]
--       refine mem_nhdsWithin_Ici_iff_exists_Ico_subset.mpr ?_
--       use (min (u + c) (n + 1))
--       constructor
--       · apply Set.mem_Iio.2
--         rw [Set.mem_Ico] at h'
--         apply lt_min
--         exact lt_add_of_pos_right u hc
--         exact h'.2
--       · rw [Set.subset_def]
--         intro y hy
--         dsimp
--         calc
--         _ = |(y - u) * phiDerivReal' K L u - (phiReal K K' (phiReal K' L y) - phiReal K K' (phiReal K' L u))| := by
--           rw [← abs_neg]
--           ring_nf
--         _ ≤ |(y - u) * (phiDerivReal' K L u - phiDerivReal' K L y)| := by
--           apply abs_le_abs_of_nonneg
--           · simp only [sub_nonneg]
--             apply le_trans
--             · apply phiReal_sub_phiReal_le' K K' ((phiReal_StrictMono K' L).monotone (Set.mem_Ico.1 hy).1)
--             · calc
--               _ ≤ (y - u) * (phiDerivReal' K' L u) * (phiDerivReal' K K' (phiReal K' L u)) := by
--                 rw [mul_le_mul_right]
--                 apply phiReal_sub_phiReal_le' K' L (Set.mem_Ico.1 hy).1
--                 unfold phiDerivReal'
--                 simp only [Nat.cast_pos, Nat.card_pos, div_pos_iff_of_pos_left]
--               _ = _ := by
--                 rw [mul_assoc, mul_eq_mul_left_iff]
--                 left
--                 apply phiDerivReal'_comp
--                 sorry
--           · simp only [mul_sub, sub_eq_add_neg ((y - u) * (phiDerivReal' K L u)), add_le_add_iff_left, neg_le_neg_iff]
--             calc
--             _ = (y - u) * (phiDerivReal' K' L y) * (phiDerivReal' K K' (phiReal K' L y)) := by
--               rw [mul_assoc, phiDerivReal'_comp K K' L (u := y)]
--               sorry
--             _ ≤ (phiReal K' L y - phiReal K' L u) * (phiDerivReal' K K' (phiReal K' L y)) := by
--               rw [mul_le_mul_right]
--               apply le_phiReal_sub_phiReal' K' L (Set.mem_Ico.1 hy).1
--               unfold phiDerivReal'
--               simp only [Nat.cast_pos, Nat.card_pos, div_pos_iff_of_pos_left]
--             _ ≤ _ := by
--               apply le_phiReal_sub_phiReal' K K' ((phiReal_StrictMono K' L).monotone (Set.mem_Ico.1 hy).1)
--         _ ≤ _ := by
--           simp only [abs_mul]
--           rw [mul_comm]
--           by_cases hc' : y = u
--           · simp only [hc', sub_self, abs_zero, mul_zero, le_refl]
--           · rw [mul_le_mul_right]
--             · calc
--               _ ≤ |y - u| := by
--                 apply abs_le_abs_of_nonneg
--                 linarith [phiDerivReal'_antitone K L (Set.mem_Ico.1 hy).1]
--                 have h1 : ⌊u⌋ = n := by
--                   apply Int.floor_eq_iff.2
--                   simp only [Int.cast_natCast]
--                   constructor
--                   · apply (Set.mem_Ico.1 h').1
--                   · apply (Set.mem_Ico.1 h').2
--                 have h : ⌊u⌋ = ⌊y⌋ := by
--                   rw [h1]
--                   symm
--                   apply Int.floor_eq_iff.2
--                   simp only [Int.cast_natCast]
--                   constructor
--                   · apply le_trans (Set.mem_Ico.1 h').1 (Set.mem_Ico.1 hy).1
--                   · exact (lt_min_iff.1 (Set.mem_Ico.1 hy).2).2
--                 rw [phiDerivReal', phiDerivReal', h, sub_self]
--                 simp only [sub_nonneg, ge_iff_le]
--                 exact (Set.mem_Ico.1 hy).1
--               _ ≤ _ := by
--                 apply abs_le.2
--                 constructor
--                 · apply le_of_lt (lt_of_lt_of_le (b := 0) _ _)
--                   linarith [hc]
--                   linarith [(Set.mem_Ico.1 hy).1]
--                 · apply le_of_lt
--                   linarith [(lt_min_iff.1 (Set.mem_Ico.1 hy).2).1]
--             · apply abs_pos.2 (sub_ne_zero.2 hc')
--   }
--   exact h

variable {f g : Filter ℝ}

set_option maxHeartbeats 0

#check ContinuousOn.mul
#check ContinuousOn.add
#check ContinuousWithinAt.mul
#check ContinuousOn.congr
#check Set.EqOn

theorem phiReal_linear_section {n : ℕ} {x : ℝ} (h : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ)) : phiReal K L x = phiReal K L n + (1 / Nat.card G(L/K)_[0] : ℝ) * (Nat.card G(L/K)_[(n + 1)]) * (x - n) := by
  by_cases hc : x = n
  · simp only [hc, sub_self, one_div, mul_zero, add_zero]
  · have hc' : ⌈x⌉ = n + 1 := by
      apply Int.ceil_eq_iff.2
      simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, add_sub_cancel_right]
      refine ⟨lt_of_le_of_ne (Set.mem_Icc.1 h).1 ?_, (Set.mem_Icc.1 h).2⟩
      exact fun a ↦ hc (id (Eq.symm a))
    have hx : 0 < x := by
      apply lt_of_le_of_lt (b := (n : ℝ))
      exact Nat.cast_nonneg' n
      apply lt_of_le_of_ne (Set.mem_Icc.1 h).1
      exact fun a ↦ hc (id (Eq.symm a))
    by_cases hc'' : n = 0
    · rw [phiReal_eq_sum_card K L (le_of_lt hx)]
      simp only [hc', hc'', one_div, CharP.cast_eq_zero, zero_add, sub_self, zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, max_self, Int.cast_zero, sub_zero, phiReal_zero_eq_zero, zero_add]
      ring
    · rw [phiReal_eq_sum_card K L (le_of_lt hx), hc', phiReal_eq_sum_card', Int.floor_natCast]
      simp only [one_div, add_sub_cancel_right, Nat.cast_sum, Nat.cast_nonneg, max_eq_right, Int.cast_natCast, sub_self, zero_mul, add_zero, mul_add]
      congr 1
      ring
      apply lt_of_le_of_ne (Nat.cast_nonneg' n)
      symm
      simp only [ne_eq, Nat.cast_eq_zero, hc'', not_false_eq_true]

#check HasDerivWithinAt.add
#check HasDerivWithinAt.congr
#check hasDerivWithinAt_Ioi_iff_Ici

theorem phiReal_HasDerivWithinAt {u : ℝ} (h : 0 ≤ u) : HasDerivWithinAt (phiReal K L) (phiDerivReal' K L u) (Set.Ici u) u := by
  have hu : ⌊u⌋.toNat = ⌊u⌋ := by
    apply Int.toNat_of_nonneg
    apply Int.floor_nonneg.2 h
  apply hasDerivWithinAt_Ioi_iff_Ici.1
  apply (HasDerivWithinAt.Ioi_iff_Ioo (y := (⌊u⌋ : ℝ) + 1) _).1
  apply HasDerivWithinAt.congr (f := fun x => phiReal K L ⌊u⌋ + (1 / Nat.card G(L/K)_[0] : ℝ) * (Nat.card G(L/K)_[(⌊u⌋ + 1)]) * (x - ⌊u⌋))
  apply HasDerivWithinAt.congr_deriv (f' := 0 + (Nat.card G(L/K)_[(⌊u⌋ + 1)] : ℝ) / (Nat.card G(L/K)_[0] : ℝ))
  apply HasDerivWithinAt.add
  apply hasDerivWithinAt_const
  apply HasDerivWithinAt.congr_deriv (f' := (1 / Nat.card G(L/K)_[0] : ℝ) * (Nat.card G(L/K)_[(⌊u⌋ + 1)]) * 1)
  apply HasDerivWithinAt.const_mul
  apply HasDerivWithinAt.sub_const
  apply hasDerivWithinAt_id
  simp only [one_div, mul_one, ← div_eq_inv_mul]
  unfold phiDerivReal'
  rw [zero_add]
  intro x hx
  rw [phiReal_linear_section K L (n := ⌊u⌋.toNat) (x := x), ← Int.cast_natCast, hu]
  rw [← Int.cast_natCast, hu, Set.mem_Icc]
  refine ⟨le_of_lt (lt_of_le_of_lt (Int.floor_le u) (Set.mem_Ioo.1 hx).1), le_of_lt (Set.mem_Ioo.1 hx).2⟩
  rw [phiReal_linear_section K L (n := ⌊u⌋.toNat) (x := u), ← Int.cast_natCast, hu]
  rw [← Int.cast_natCast, hu, Set.mem_Icc]
  refine ⟨Int.floor_le u, le_of_lt (Int.lt_floor_add_one u)⟩
  exact Int.lt_floor_add_one u


#check phiDerivReal'_comp
theorem phiReal_comp_HasDerivWithinAt {u : ℝ} (h : 0 ≤ u) : HasDerivWithinAt (phiReal K K' ∘ phiReal K' L) (phiDerivReal' K L u) (Set.Ici u) u := by
  apply HasDerivWithinAt.congr_deriv (f' := phiDerivReal' K' L u * phiDerivReal' K K' (phiReal K' L u))
  apply HasDerivWithinAt.scomp (t' := Set.Ici (phiReal K' L u))
  apply phiReal_HasDerivWithinAt
  rw [← phiReal_zero_eq_zero K' L]
  apply (phiReal_StrictMono K' L).monotone h
  apply phiReal_HasDerivWithinAt K' L h
  apply Monotone.mapsTo_Ici (phiReal_StrictMono K' L).monotone
  by_cases hu : 0 < u
  · rw [← phiDerivReal'_comp K K' L hu]
  · have hu' : u = 0 := Eq.symm (eq_of_le_of_not_lt h hu)
    rw [hu', phiDerivReal'_comp_zero K K' L]

theorem phiReal_continuousOn_section {n : ℕ} : ContinuousOn (phiReal K L) (Set.Icc (n : ℝ) (n + 1 : ℝ)) := by
  let g : ℝ → ℝ := fun x => phiReal K L n + (1 / Nat.card G(L/K)_[0] : ℝ) * (Nat.card G(L/K)_[(n + 1)]) * (x - n)
  apply ContinuousOn.congr (f := g)
  apply ContinuousOn.add (continuousOn_const)
  apply ContinuousOn.mul (continuousOn_const)
  apply ContinuousOn.add (continuousOn_id' (Set.Icc (n : ℝ) (n + 1 : ℝ))) (continuousOn_const)
  intro x hx
  apply phiReal_linear_section K L hx


-- def piecewiselinear (u : ℝ) : ∑ x in Finset.Icc 1 (⌈u⌉ - 1), (g x) + (u - ⌈u⌉ + 1) * (g ⌈u⌉) := by sorry

#check continuousOn_finset_sum
#check continuousAt_iff_continuous_left_right
#check continuous_iff_continuousAt
#check ContinuousWithinAt.mul
#check ContinuousWithinAt.add
#check ContinuousWithinAt.congr
#check ContinuousWithinAt.sub
theorem phiReal_left_continuous {x : ℝ} : ContinuousWithinAt (phiReal K L) (Set.Iic x) x := by
  by_cases hc : x ≤ 0
  · apply ContinuousWithinAt.congr (f := fun t => t) (continuousWithinAt_id)
    intro y hy
    rw [phiReal_eq_self_of_le_zero]
    apply le_trans (Set.mem_Iic.1 hy) hc
    rw [phiReal_eq_self_of_le_zero K L hc]
  · push_neg at hc
    have hx : (⌈x⌉ - 1).toNat = ⌈x⌉ - 1 := by
      apply Int.toNat_of_nonneg
      apply Int.le_of_sub_one_lt
      simp only [zero_sub, Int.reduceNeg, neg_lt_sub_iff_lt_add, lt_add_iff_pos_right, Int.ceil_pos]
      exact hc
    apply (continuousWithinAt_Icc_iff_Iic (a := (⌈x⌉ - 1 : ℝ)) _).1
    apply ContinuousWithinAt.congr (f := fun t => (phiReal K L (⌈x⌉ - 1)) + ((1 / (Nat.card G(L/K)_[0] : ℝ)) * (Nat.card G(L/K)_[(⌈x⌉)] : ℝ)) * (t - (⌈x⌉ - 1)))
    apply ContinuousWithinAt.add (continuousWithinAt_const)
    apply ContinuousWithinAt.mul (continuousWithinAt_const)
    apply ContinuousWithinAt.sub (continuousWithinAt_id) (continuousWithinAt_const)
    intro y hy
    rw [phiReal_linear_section K L (n := (⌈x⌉ - 1).toNat) (x := y), ← Int.cast_natCast, hx, sub_add_cancel, Int.cast_sub, Int.cast_one]
    rw [← Int.cast_natCast, hx, Int.cast_sub, Int.cast_one, sub_add_cancel,  Set.mem_Icc]
    refine ⟨(Set.mem_Icc.1 hy).1, le_trans (Set.mem_Icc.1 hy).2 (Int.le_ceil x)⟩
    rw [phiReal_linear_section K L (n := (⌈x⌉ - 1).toNat), ← Int.cast_natCast, hx, Int.cast_sub, Int.cast_one, one_div, sub_add_cancel]
    rw [← Int.cast_natCast, hx, Int.cast_sub, Int.cast_one, sub_add_cancel, Set.mem_Icc]
    refine ⟨by linarith [Int.ceil_lt_add_one x], Int.le_ceil x⟩
    linarith [Int.ceil_lt_add_one x]


theorem phiReal_right_continuous {x : ℝ} : ContinuousWithinAt (phiReal K L) (Set.Ici x) x := by
  apply (continuousWithinAt_Icc_iff_Ici (b := (⌊x⌋ + 1 : ℝ)) _).1
  by_cases hc : x < 0
  ·
    apply ContinuousWithinAt.congr (f := fun t => t) (continuousWithinAt_id)
    intro y hy
    apply phiReal_eq_self_of_le_zero
    apply le_trans (Set.mem_Icc.1 hy).2
    rw [← Int.cast_one (R := ℝ), ← Int.cast_add, ← Int.cast_zero (R := ℝ), Int.cast_le]
    apply Int.le_of_sub_one_lt
    rw [add_sub_cancel_right]
    apply_mod_cast lt_of_le_of_lt (Int.floor_le x) hc
    apply phiReal_eq_self_of_le_zero K L (le_of_lt hc)
  · push_neg at hc
    have hx : ⌊x⌋.toNat = ⌊x⌋ := Int.toNat_of_nonneg (Int.floor_nonneg.2 hc)
    apply ContinuousWithinAt.congr (f := fun t => (phiReal K L ⌊x⌋) + ((1 / (Nat.card G(L/K)_[0] : ℝ)) * (Nat.card G(L/K)_[(⌊x⌋ + 1)] : ℝ)) * (t - ⌊x⌋))
    apply ContinuousWithinAt.add (continuousWithinAt_const)
    apply ContinuousWithinAt.mul (continuousWithinAt_const)
    apply ContinuousWithinAt.sub (continuousWithinAt_id) (continuousWithinAt_const)
    intro y hy
    rw [phiReal_linear_section K L (n := ⌊x⌋.toNat), ← Int.cast_natCast, hx]
    rw [← Int.cast_natCast, hx, Set.mem_Icc]
    refine ⟨le_trans (Int.floor_le x) (Set.mem_Icc.1 hy).1, (Set.mem_Icc.1 hy).2⟩
    rw [phiReal_linear_section K L (n := ⌊x⌋.toNat), ← Int.cast_natCast, hx]
    rw [← Int.cast_natCast, hx, Set.mem_Icc]
    refine ⟨Int.floor_le x, le_of_lt (Int.lt_floor_add_one x)⟩
  exact Int.lt_floor_add_one x



theorem phiReal_Continuous : Continuous (phiReal K L) := by
  apply continuous_iff_continuousAt.2
  intro x
  apply continuousAt_iff_continuous_left_right.2
  constructor
  · exact phiReal_left_continuous K L
  · exact phiReal_right_continuous K L

theorem phiReal_comp_continuousOn_section {n : ℕ} : ContinuousOn (phiReal K K' ∘ phiReal K' L) (Set.Icc (n : ℝ) (n + 1 : ℝ)) := by
  show ContinuousOn (fun x => phiReal K K' (phiReal K' L x)) (Set.Icc (n : ℝ) (n + 1 : ℝ))
  apply Continuous.comp_continuousOn'
  apply phiReal_Continuous
  apply phiReal_continuousOn_section


  -- apply ContinuousOn.congr (f := fun x => 1 / (Nat.card G(K'/K)_[0] ) * ((∑ i ∈ Finset.Icc 1 (⌈phiReal K' L x⌉ - 1), Nat.card G(K'/K)_[i]) + (phiReal K' L x - (max 0 (⌈phiReal K' L x⌉ - 1))) * (Nat.card G(K'/K)_[⌈phiReal K' L x⌉])))
  -- apply ContinuousOn.mul (continuousOn_const)
  -- apply ContinuousOn.add
  -- simp only [Nat.cast_sum]
  -- sorry

  -- change ContinuousOn (fun x => (phiReal K K' (phiReal K' L x))) (Set.Icc (n : ℝ) (n + 1 : ℝ))


  -- apply ContinuousOn.comp'' (t := Set.Icc (phiReal K' L n) (phiReal K' L (n + 1)))
  -- dsimp [ContinuousOn]


  -- let g : ℝ → ℝ := fun x => phiReal K K' (phiReal K' L n) + (1 / Nat.card G(K'/K)_[0] : ℝ) * (Nat.card G(K'/K)_[(n + 1)] : ℝ) * phiReal K' L x
  -- let g' : ℝ → ℝ := fun x => phiReal K' L n + (1 / Nat.card G(L/K')_[0] : ℝ) * (Nat.card G(L/K')_[(n + 1)] : ℝ) * x
  -- apply ContinuousOn.congr (f := g)
  -- apply ContinuousOn.add (continuousOn_const)
  -- apply ContinuousOn.mul (continuousOn_const)
  -- apply ContinuousOn.congr (f := g')
  -- apply ContinuousOn.add (continuousOn_const)
  -- apply ContinuousOn.mul (continuousOn_const) (continuousOn_id' (Set.Icc (n : ℝ) (n + 1 : ℝ)))
  -- intro x hx
  -- dsimp [g']


  -- intro x hx u hu
  -- apply Filter.mem_map'.2
  -- constructor

  -- apply eventually_iff.mp ?_
  -- constructor

  -- use ((fun x => phiReal K K' (phiReal K' L x))⁻¹' u) ∩ (Set.Icc (n : ℝ) (n + 1 : ℝ))
  -- constructor
  -- · apply?
  -- · sorry


  -- apply tendsto_nhds_of_eventually_eq
  -- use {x}
  -- constructor
  -- · refine mem_nhds_iff.mpr ?h.left.a
  --   use {x}
  --   constructor
  --   · rfl
  --   · constructor
  --     · sorry
  --     · rfl
  -- use Set.Icc (n : ℝ) (n + 1 : ℝ)
  -- constructor
  -- · apply mem_principal_self
  -- · have h : {x} ∩ Set.Icc (n : ℝ) (n + 1 : ℝ) = {x} := by sorry
  --   simp only [h]
  --   ext t
  --   constructor
  --   · intro ht
  --     sorry
  --   · intro ht
  --     sorry

theorem phiReal_comp_of_isVal_Extension_pos_aux {n : ℕ} : ∀ u ∈ Set.Icc (n : ℝ) (n + 1 : ℝ), ((phiReal K K') ∘ (phiReal K' L)) u = phiReal K L u := by
  induction' n with n hn
  · intro u hu
    apply eq_of_has_deriv_right_eq (a := (0 : ℝ)) (b := (1 : ℝ)) (f' := phiDerivReal' K L)
    · intro x hx
      apply phiReal_comp_HasDerivWithinAt K K' L (Set.mem_Ico.1 hx).1
    · intro x hx
      apply phiReal_HasDerivWithinAt K L (Set.mem_Ico.1 hx).1
    · convert phiReal_comp_continuousOn_section K K' L (n := 0)
      simp only [CharP.cast_eq_zero]
      simp only [CharP.cast_eq_zero, zero_add]
    · convert phiReal_continuousOn_section K L (n := 0)
      simp only [CharP.cast_eq_zero]
      simp only [CharP.cast_eq_zero, zero_add]
    · rw [Function.comp_apply, phiReal_zero_eq_zero, phiReal_zero_eq_zero, phiReal_zero_eq_zero]
    · simp only [CharP.cast_eq_zero, zero_add] at hu
      exact hu
  · intro u hu
    apply eq_of_has_deriv_right_eq (a := (n + 1 : ℝ)) (b := (n + 2 : ℝ)) (f' := phiDerivReal' K L)
    · intro x hx
      apply phiReal_comp_HasDerivWithinAt K K' L (le_trans _ (Set.mem_Ico.1 hx).1)
      apply le_trans (Nat.cast_nonneg' n) (by linarith)
    · intro x hx
      apply phiReal_HasDerivWithinAt K L (le_trans _ (Set.mem_Ico.1 hx).1)
      apply le_trans (Nat.cast_nonneg' n) (by linarith)
    · convert phiReal_comp_continuousOn_section K K' L (n := n + 1) using 1
      simp only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
    · convert phiReal_continuousOn_section K L (n := n + 1) using 1
      simp only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
    · apply hn (n + 1 : ℝ)
      simp only [Set.mem_Icc, le_add_iff_nonneg_right, zero_le_one, le_refl, and_self]
    · simp only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] at hu
      exact hu


-- theorem phiReal_comp_of_isValExtension_aux {u : ℝ} : ((phiReal K K') ∘ (phiReal K' L)) u = phiReal K L u := by
--   have hdf : ∀ x ∈ Set.Ioc (⌊u⌋ : ℝ) (⌊u⌋ + 1 : ℝ), HasDerivWithinAt (phiReal K K' ∘ phiReal K' L) (phiDerivReal K L x) (Set.Iic x) x := by
--     intro x hx
--     unfold HasDerivWithinAt HasDerivAtFilter
--     haveI h : HasFDerivAtFilter (𝕜 := ℝ) ((phiReal K K') ∘ (phiReal K' L)) (ContinuousLinearMap.smulRight (S := ℝ) 1 (phiDerivReal K L x)) x (nhdsWithin x (Set.Iic x)) := {
--       isLittleO := by
--         dsimp
--         rw [IsLittleO_def]
--         intro c hc
--         rw [IsBigOWith_def, eventually_iff]
--         refine mem_nhdsWithin_Iic_iff_exists_Ioc_subset.mpr ?_
--         use ⌊u⌋
--         constructor
--         · apply Set.mem_Ioi.2
--           rw [Set.mem_Ioc] at hx
--           exact hx.1
--         · rw [Set.subset_def]
--           intro y hy
--           dsimp
--           -- have h1 : phiReal K K' (phiReal K' L y) - phiReal K K' (phiReal K' L x) ≤ (phiReal K' L y - phiReal K' L x) * phiDerivReal K K' (phiReal K' L x) := by
--           --   apply phiReal_sub_phiReal_le μ K K' (v := phiReal K' L y) (u := phiReal K' L x)
--           --   sorry
--           -- have h2 : phiReal K' L y - phiReal K' L x ≤ (y - x) * phiDerivReal K' L (x) := by
--           --   apply phiReal_sub_phiReal_le μ K' L
--           --   sorry
--           have h1 : phiReal K K' (phiReal K' L x) - phiReal K K' (phiReal K' L y) ≤ (x - y) * (phiDerivReal K' L y) * phiDerivReal K K' (phiReal K' L y) := by
--             apply le_trans (phiReal_sub_phiReal_le K K' (u := phiReal K' L y) (v := phiReal K' L x) ?_)
--             apply (mul_le_mul_right ?_).2
--             apply phiReal_sub_phiReal_le K' L (u := y) (v := x) ?_
--             obtain ⟨hy1, hy2⟩ := Set.mem_Ioc.1 hy
--             exact hy2
--             apply phiDerivReal_pos K K'
--             apply (phiReal_StrictMono K' L).monotone (Set.mem_Ioc.1 hy).2
--           have h2 : (x - y) * (phiDerivReal K' L x) * phiDerivReal K K' (phiReal K' L x) ≤ phiReal K K' (phiReal K' L x) - phiReal K K' (phiReal K' L y) := by
--             apply le_trans ?_ (le_phiReal_sub_phiReal K K' (u := phiReal K' L y) (v := phiReal K' L x) ?_)
--             apply (mul_le_mul_right ?_).2
--             apply le_phiReal_sub_phiReal K' L (Set.mem_Ioc.1 hy).2
--             apply phiDerivReal_pos
--             apply (phiReal_StrictMono K' L).monotone (Set.mem_Ioc.1 hy).2
--           rw [mul_assoc, phiDerivReal_comp] at h1
--           rw [mul_assoc, phiDerivReal_comp] at h2
--           have h3 : (phiReal K K' (phiReal K' L x) - phiReal K K' (phiReal K' L y)) - (x - y) * phiDerivReal K L x ≤ (x - y) * phiDerivReal K L y - (x - y) * phiDerivReal K L x := by
--             exact tsub_le_tsub_right h1 ((x - y) * phiDerivReal K L x)
--           have h4 : |(phiReal K K' (phiReal K' L x) - phiReal K K' (phiReal K' L y)) - (x - y) * phiDerivReal K L x| ≤ |(x - y) * phiDerivReal K L y - (x - y) * phiDerivReal K L x| := by
--             apply abs_le_abs_of_nonneg
--             rw [sub_nonneg]
--             exact h2
--             simp only [neg_sub, h3]
--           by_cases hcase : y = x
--           · simp only [hcase, sub_self, zero_mul, abs_zero, mul_zero, le_refl]
--           · rw [← abs_neg]
--             have : (-(phiReal K K' (phiReal K' L y) - phiReal K K' (phiReal K' L x) - (y - x) * phiDerivReal K L x)) = phiReal K K' (phiReal K' L x) - phiReal K K' (phiReal K' L y) - (x - y) * phiDerivReal K L x := by ring
--             rw [this]
--             apply le_trans h4
--             rw [← mul_sub, abs_mul, mul_comm, ← abs_neg (x - y), neg_sub, mul_le_mul_right]
--             have h : ⌈x⌉ = ⌈y⌉ := by
--               apply (Int.ceil_eq_ceil ?_ ?_)
--               apply (Set.mem_Ioc.1 hy).2
--               simp only [tsub_le_iff_right, sub_add_cancel]
--               sorry
--               --apply le_of_lt (Set.mem_Ico.1 hy).2
--             rw [phiDerivReal, phiDerivReal, h, sub_self, abs_zero]
--             apply le_of_lt hc
--             apply abs_pos.2
--             simp only [ne_eq, sub_ne_zero]
--             exact hcase
--     }
--     exact h
--   have hdg : ∀ x ∈ Set.Ioc (⌊u⌋ : ℝ) (⌊u⌋ + 1 : ℝ), HasDerivWithinAt (phiReal K L) (phiDerivReal K L x) (Set.Iic x) x := by
--     intro x hx
--     unfold HasDerivWithinAt HasDerivAtFilter
--     haveI h : HasFDerivAtFilter (𝕜 := ℝ) (phiReal K L) (ContinuousLinearMap.smulRight (S := ℝ) 1 (phiDerivReal K L x)) x (nhdsWithin x (Set.Iic x)) := {
--       isLittleO := by
--         dsimp
--         rw [IsLittleO_def]
--         intro c hc
--         rw [IsBigOWith_def, eventually_iff]
--         refine mem_nhdsWithin_Iic_iff_exists_Ioc_subset.mpr ?_
--         use ⌊u⌋
--         constructor
--         · apply Set.mem_Ioi.2
--           rw [Set.mem_Ioc] at hx
--           exact hx.1
--         · rw [Set.subset_def]
--           intro y hy
--           dsimp
--           by_cases hcase : 0 < x
--           · have hcase' : 0 < y := by sorry
--             have h : ⌈x⌉ = ⌈y⌉ := by sorry
--             rw [phiReal_eq_sum_card K L hcase, phiReal_eq_sum_card K L hcase', phiDerivReal, h, max_eq_right, max_eq_right]
--             ring
--             simp only [abs_zero, hc, mul_nonneg_iff_of_pos_left, abs_nonneg]
--             exact Int.ceil_nonneg (le_of_lt hcase')
--             sorry
--           · push_neg at hcase
--             have hcase' : y ≤ 0 := by sorry
--             rw [phiReal_eq_self_of_le_zero K L hcase, phiReal_eq_self_of_le_zero K L hcase', phiDerivReal, max_eq_left, div_self]
--             ring
--             simp only [abs_zero, hc, mul_nonneg_iff_of_pos_left, abs_nonneg]
--             · apply ne_of_gt
--               simp only [Nat.cast_pos, Nat.card_pos]
--             · refine Int.ceil_le.mpr ?_
--               rw [Int.cast_zero]
--               exact hcase
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
--     -- rw [eventually_iff]
--     -- have h : {x_1 | phiReal K L x_1 = phiReal K L x} = {x} := by
--     --   ext t
--     --   constructor
--     --   · simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
--     --     sorry
--     --   · simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
--     --     intro h
--     --     rw [h]
--     -- rw [h]
--     -- dsimp [nhdsWithin]
--     -- apply mem_inf_of_left
--     -- rw [nhds, Filter.mem_iInf]
--     --apply Filter.le_iff_forall_inf_principal_compl.2
--   apply eq_of_has_deriv_left_eq hdf hdg hcf hcg

--   --------------------------------------------------------------------------------------
--   · sorry
--   simp only [Set.mem_Icc]
--   constructor
--   · exact Int.floor_le u
--   · sorry
