import RamificationGroup.HerbrandFunction
import Mathlib.RingTheory.Valuation.Basic

open scoped Classical
open HerbrandFunction DiscreteValuation AlgEquiv Valued
open DiscreteValuation Subgroup Set Function Finset BigOperators Int Valued

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [vK : Valued K ℤₘ₀] [Valuation.IsDiscrete vK.v] [vL : Valued L ℤₘ₀] [Valuation.IsDiscrete vL.v] [Algebra K L] [IsValExtension vK.v vL.v] [FiniteDimensional K L] [CompleteSpace K] [Algebra.IsSeparable K L] [Algebra (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])]
[Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])]

theorem Int.aux {a b : ℤ} (h1 : a ≤ b) (h2 : b < a + 1) : a = b := by
  by_contra hc
  have h3 : a < b := by exact lt_of_le_of_ne h1 hc
  have h4 : a + 1 ≤ b := by exact h3
  absurd h4; push_neg; exact h2

set_option maxHeartbeats 0

theorem truncatedLowerindex_eq_if_aux {i : ℤ} {u : ℚ} {s : (L ≃ₐ[K] L)} (hgt : 0 ≤ u) (hgt' : -1 ≤ i) (hu : i ≤ (⌈u⌉ - 1)) (hs : s ∈ HerbrandFunction.Ramification_Group_diff K L i) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : i_[L/K]ₜ (u + 1) s = i + 1 := by
  unfold Ramification_Group_diff at hs
  simp only [Set.toFinset_diff, Finset.mem_sdiff, Set.mem_toFinset, SetLike.mem_coe] at hs
  rcases hs with ⟨hs1, hs2⟩
  have h1 : i + 1 ≤ i_[L/K]ₜ (u + 1) s := by
    have h1' : i ≤ i_[L/K]ₜ (u + 1) s - 1 := by
      apply (le_truncatedLowerIndex_sub_one_iff_mem_lowerRamificationGroup s i (u + 1)  _ hgen).2
      · simp only [ceil_intCast, hs1]
      · simp only [add_le_add_iff_right]
        apply le_of_lt; apply Int.add_one_le_ceil_iff.1; linarith [hu]
    linarith [h1']
  have h2 : i_[L/K]ₜ (u + 1) s < i + 2 := by
    by_contra hc; push_neg at hc
    have h : s ∈ decompositionGroup K L := by exact mem_decompositionGroup s
    have hs2' : s ∈ G(L/K)_[⌈i + 1⌉] := by
      convert mem_lowerRamificationGroup_of_le_truncatedLowerIndex_sub_one h (u := ((i : ℤ) + 1)) hgen (by linarith [hc])
      simp only [ceil_add_one, ceil_int, id_eq, ceil_intCast]
    apply hs2
    simp only [ceil_add_one, ceil_int, id_eq] at hs2'; exact hs2'
  have h3 : i_[L/K] s ≠ ⊤ := by
    by_contra hc
    rw [lowerIndex_eq_top_iff_eq_refl (by apply mem_decompositionGroup)] at hc
    have hs2' : s ∈ G(L/K)_[(i + 1)] := by
      rw [hc]; apply Subgroup.one_mem
    apply hs2 hs2'
  have h4 : i_[L/K]ₜ (u + 1) s = ↑(WithTop.untop (i_[L/K] s) (of_eq_false (eq_false h3) : ¬ i_[L/K] s = ⊤)) := by
    unfold AlgEquiv.truncatedLowerIndex
    simp only [h3, ↓reduceDIte, min_eq_right_iff, ge_iff_le]
    apply le_of_lt
    -- have h : i_[L/K] s < i.toNat + 1 + 1 := by
    --   by_contra hc; push_neg at hc
    --   have hs2' : s ∈ G(L/K)_[(i.toNat + 1)] := by
    --     apply (mem_lowerRamificationGroup_iff_of_generator (K := K) (L := L) hgen (s := s) ?_ (i.toNat + 1)).2 hc
    --     · apply mem_decompositionGroup s
    --   by_cases hc : 0 ≤ i
    --   · rw [Int.toNat_of_nonneg hc] at hs2'
    --     apply hs2 hs2'
    --   · have hi : i = -1 := by
    --       symm
    --       apply eq_iff_le_not_lt.2
    --       constructor
    --       · exact hgt'
    --       · linarith [hc]
    --     simp only [hi, reduceNeg, reduceToNat, CharP.cast_eq_zero, zero_add] at hs2'
    --     simp only [hi, reduceNeg, add_left_neg] at hs2
    --     have hs2'' : s ∈ G(L/K)_[0] := by
    --       apply mem_of_subset_of_mem ?_ hs2'
    --       apply lowerRamificationGroup.antitone
    --       linarith
    --     apply hs2 hs2''
    have h : i_[L/K] s < (i + 1).toNat + 1 := by
      by_contra hc
      push_neg at hc
      have hi : 0 ≤ i + 1 := by linarith [hgt']
      have hs2' : s ∈ G(L/K)_[(i + 1).toNat] := by
        apply (mem_lowerRamificationGroup_iff_of_generator hgen ?_ (i + 1).toNat).2
        exact hc
        apply mem_decompositionGroup s
      rw [Int.toNat_of_nonneg hi] at hs2'
      apply hs2 hs2'
    have h' : (i + 1).toNat ≤ i_[L/K] s := by
      by_contra hc
      push_neg at hc
      have h1' : i_[L/K]ₜ (u + 1) s < i + 1 := by
        unfold AlgEquiv.truncatedLowerIndex
        simp only [h3, ↓reduceDIte, min_lt_iff, add_lt_add_iff_right]
        right
        rw [← Int.cast_one, ← cast_add, ← Int.cast_natCast, cast_lt, ← Int.toNat_of_nonneg (a := i + 1), Nat.cast_lt]
        apply (WithTop.untop_lt_iff _).2
        exact hc
        linarith [hgt']
      absurd h1
      push_neg
      exact h1'
    have hilk : i_[L/K] s = (i + 1).toNat := by
      by_cases hc : 1 ≤ i + 1
      · apply (ENat.toNat_eq_iff _).1
        apply Nat.eq_of_lt_succ_of_not_lt
        · rw [← Nat.cast_lt (α := ℕ∞), ENat.coe_toNat h3, Nat.cast_add, Nat.cast_one]
          exact h
        · push_neg
          rw [← Nat.cast_le (α := ℕ∞), ENat.coe_toNat h3]
          exact h'
        simp only [ne_eq, toNat_eq_zero, not_le]
        linarith [hc]
      · have hi : i = -1 := by
          symm; apply eq_iff_le_not_lt.2; constructor
          · exact hgt'
          · linarith [hc]
        simp only [hi, reduceNeg, neg_add_cancel, toNat_zero, CharP.cast_eq_zero]
        by_contra hcon
        have hilk : 1 ≤ i_[L/K] s := by
          apply ENat.one_le_iff_ne_zero.2 hcon
        simp only [hi, reduceNeg, neg_add_cancel, toNat_zero, CharP.cast_eq_zero, zero_add] at h
        absurd h; push_neg
        exact hilk
    apply lt_of_le_of_lt (b := (⌈u⌉.toNat : ℚ))
    · rw [Nat.cast_le]
      apply (WithTop.untop_le_iff h3).2
      rw [hilk, ENat.some_eq_coe, Nat.cast_le]
      apply toNat_le_toNat
      linarith [hu]
    · rw [← Int.cast_natCast, Int.toNat_of_nonneg]
      exact ceil_lt_add_one u
      exact ceil_nonneg hgt
    -- by_cases hc : 0 ≤ i
    -- · have hilk : i_[L/K] s = i.toNat + 1 := by
    --     have h' : i.toNat + 1 ≤ i_[L/K] s := by sorry
    --     rw [← Nat.cast_one, ← Nat.cast_add]
    --     apply (ENat.toNat_eq_iff _).1
    --     apply Nat.eq_of_lt_succ_of_not_lt
    --     · sorry
    --     · sorry
    --     simp only [ne_eq, add_eq_zero, toNat_eq_zero, one_ne_zero, and_false, not_false_eq_true]
    --   have hilk' : i_[L/K] s ≤ ⌈u⌉.toNat := by
    --     rw [hilk, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le, ← Nat.cast_le (α := ℤ), Nat.cast_add, Int.toNat_of_nonneg hc, Int.toNat_of_nonneg, Nat.cast_one]
    --     linarith [hu]
    --     exact ceil_nonneg hgt
    --   apply lt_of_le_of_lt (b := (⌈u⌉.toNat : ℚ))
    --   · simp only [Nat.cast_le]
    --     apply (WithTop.untop_le_iff h3).2
    --     exact hilk'
    --   · rw [← Int.cast_natCast, Int.toNat_of_nonneg]
    --     exact ceil_lt_add_one u
    --     exact ceil_nonneg hgt
    -- · have hi : i = -1 := by
    --       symm
    --       apply eq_iff_le_not_lt.2
    --       constructor
    --       · exact hgt'
    --       · linarith [hc]
    --   have hilk : i_[L/K] s = 0 := by
    --     sorry
    --   simp only [hilk, WithTop.untop_zero, CharP.cast_eq_zero, gt_iff_lt]
    --   exact add_pos_of_nonneg_of_pos hgt rfl
    -- have h' : i_[L/K] s < ⌈u⌉.toNat + 1 := by
    --   apply lt_of_lt_of_le h
    --   by_cases hc : 0 ≤ i
    --   · sorry
    --   · have hi : i = -1 := by
    --       symm
    --       apply eq_iff_le_not_lt.2
    --       constructor
    --       · exact hgt'
    --       · linarith [hc]
    --     simp only [hi, reduceNeg, reduceToNat, CharP.cast_eq_zero, zero_add, ge_iff_le]
    --     sorry
    -- apply Int.lt_ceil.1
    -- rw [ceil_add_one, ← Int.toNat_of_nonneg (a := ⌈u⌉) _, ← Nat.cast_one, ← Nat.cast_add, ofNat_eq_coe, Nat.cast_lt]
    -- apply (WithTop.untop_lt_iff h3).2
    -- simp only [WithTop.coe_add, ENat.some_eq_coe, WithTop.coe_one, h']
    -- exact ceil_nonneg hgt
    -- have h' : (WithTop.untop (i_[L/K] s) (of_eq_false (eq_false h3) : ¬ i_[L/K] s = ⊤)) < ⌈u⌉.toNat := by
    --   apply lt_of_lt_of_le (b := i.toNat + 1)
    --   · apply (WithTop.untop_lt_iff h3 (b := i.toNat + 1)).2; simp only [WithTop.coe_add, ENat.some_eq_coe, WithTop.coe_one, h]
    --   · rw [← Nat.cast_le (α := ℤ), Nat.cast_add, Int.toNat_of_nonneg (by apply ceil_nonneg hgt'), Int.toNat_of_nonneg (by apply ceil_nonneg hgt), Nat.cast_one]
    --     linarith [hu]
    -- apply lt_of_lt_of_le (b := (⌈u⌉.toNat : ℚ))
    -- · simp only [Nat.cast_lt, h']
    -- · have h1 : ⌈u⌉ ≤ u + 1 := by
    --     linarith [ceil_lt_add_one u]
    --   rw [← Int.cast_natCast, Int.toNat_of_nonneg ?_]; exact h1
    --   simp only [ceil_nonneg hgt]
  rw [h4, ← cast_one, ← cast_add (m := i) (n := 1)]
  have : (2 : ℚ) = ((2 : ℤ) : ℚ) := by simp only [cast_ofNat]
  rw [h4] at h1 h2
  have h5 : (WithTop.untop (i_[L/K] s) (of_eq_false (eq_false h3) : ¬ i_[L/K] s = ⊤)) = i + 1 := by
    symm
    apply Int.aux
    · rw [← cast_one, ← cast_add (m := i) (n := 1), ← Int.cast_natCast, cast_le] at h1
      exact h1
    · have h : (2 : ℚ) = ((2 : ℤ) : ℚ) := by simp only [cast_ofNat]
      rw [h , ← cast_add (m := i) (n := 2), ← Int.cast_natCast, cast_lt] at h2
      rw [add_assoc, one_add_one_eq_two]; exact h2
  exact Rat.ext h5 rfl

theorem sum_of_diff_aux_aux {i : ℤ} {u : ℚ} (h : i ∈ Finset.Icc (-1) (⌈u⌉ - 1)) : ∑ s in Ramification_Group_diff K L i, (AlgEquiv.truncatedLowerIndex K L (u + 1) s) = (i + 1) * (Nat.card G(L/K)_[i] - Nat.card G(L/K)_[(i + 1)]) := by
  calc
     ∑ s in Ramification_Group_diff K L i, (AlgEquiv.truncatedLowerIndex K L (u + 1) s) = ∑ s in Ramification_Group_diff K L i, ((i : ℚ) + 1) := by
      apply sum_equiv (by rfl : (L ≃ₐ[K] L) ≃ (L ≃ₐ[K] L)) (by simp)
      intro s hs
      apply truncatedLowerindex_eq_if
      obtain ⟨_, h2⟩ := Finset.mem_Icc.1 h
      exact h2
      exact hs
     _ = (i + 1) * (Nat.card G(L/K)_[i] - Nat.card G(L/K)_[(i + 1)]) := by
      simp only [sum_const, smul_add, nsmul_eq_mul, mul_comm, mul_one, Nat.card_eq_fintype_card,
        add_mul, one_mul]
      unfold Ramification_Group_diff
      have hsub : (G(L/K)_[(i + 1)] : Set (L ≃ₐ[K] L)) ⊆ (G(L/K)_[i] : Set (L ≃ₐ[K] L)) := by
        apply lowerRamificationGroup.antitone
        linarith
      have h : (((G(L/K)_[i] : Set (L ≃ₐ[K] L)) \ (G(L/K)_[(i + 1)] : Set (L ≃ₐ[K] L))).toFinset).card = ((Fintype.card G(L/K)_[i] ) - (Fintype.card G(L/K)_[(i + 1)])) := by
        rw [toFinset_diff, card_sdiff (by apply Set.toFinset_mono hsub)]
        simp only [toFinset_card, SetLike.coe_sort_coe]
      rw [h, Nat.cast_sub]
      ring
      exact Set.card_le_card hsub

theorem truncatedLowerindex_eq_of_lt {s : (L ≃ₐ[K] L)} {u : ℚ} (h : s ∈ G(L/K)_[⌈u⌉]) (hu : 0 ≤ u) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : i_[L/K]ₜ (u + 1) s = u + 1 := by
  unfold AlgEquiv.truncatedLowerIndex
  by_cases ht : i_[L/K] s = ⊤
  · simp only [ht, ↓reduceDIte]
  · simp only [ht, ↓reduceDIte, min_eq_left_iff]
    have h1 : ⌈u⌉.toNat + 1 ≤ i_[L/K] s := by
      apply (mem_lowerRamificationGroup_iff_of_generator hgen ?_ ⌈u⌉.toNat).1
      rw [Int.toNat_of_nonneg]; exact h; exact ceil_nonneg hu
      · apply mem_decompositionGroup
    have h2 : u + 1 ≤ ⌈u⌉.toNat + 1 := by
      apply (add_le_add_iff_right 1).2
      apply le_trans (b := (⌈u⌉ : ℚ))
      · exact le_ceil u
      · apply Int.cast_mono; apply self_le_toNat ⌈u⌉
    apply le_trans h2
    have h3 : ⌈u⌉.toNat + 1 ≤ WithTop.untop (i_[L/K] s) (of_eq_false (eq_false ht) : ¬ i_[L/K] s = ⊤) := by
      apply (WithTop.le_untop_iff ht).2
      simp only [WithTop.coe_add, ENat.some_eq_coe, WithTop.coe_one, h1]
    rw [← Mathlib.Tactic.Ring.inv_add (a₁ := ⌈u⌉.toNat) (a₂ := 1) rfl (by simp only [Nat.cast_one])]
    apply Nat.mono_cast h3

set_option synthInstance.maxHeartbeats 0

theorem truncatedLowerIndex_aux (u : ℚ) (hu : 0 ≤ ⌈u⌉) (x : L ≃ₐ[K] L) (hx : x ∈ G(L/K)_[⌈u⌉]) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : i_[L/K]ₜ (⌈u⌉ + 1) x = (⌈u⌉ + 1) := by
  unfold AlgEquiv.truncatedLowerIndex
  by_cases hc : i_[L/K] x = ⊤
  · simp only [hc, ↓reduceDIte]
  · simp only [hc, ↓reduceDIte, min_eq_left_iff]
    have h : ⌈u⌉.toNat + 1 ≤ WithTop.untop (i_[L/K] x) (of_eq_false (eq_false hc) : ¬ i_[L/K] x = ⊤) := by
      apply (WithTop.le_untop_iff _).2
      apply (mem_lowerRamificationGroup_iff_of_generator hgen ?_ ⌈u⌉.toNat).1
      · rw [Int.toNat_of_nonneg]; exact hx; exact hu
      · apply mem_decompositionGroup
    apply le_trans (b := (⌈u⌉.toNat + 1 : ℚ))
    · simp only [add_le_add_iff_right, ← Int.cast_natCast (R := ℚ) ⌈u⌉.toNat, Int.cast_mono (self_le_toNat ⌈u⌉)]
    · simp only [← Nat.cast_one (R := ℚ), ← Nat.cast_add (m := ⌈u⌉.toNat) (n := 1), Nat.mono_cast h]


theorem phi_eq_sum_inf_aux (u : ℚ) (hu : 0 ≤ u) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : (phi K L u) = (1 / Nat.card G(L/K)_[0]) * ((Finset.sum (⊤ : Finset (L ≃ₐ[K] L)) (AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) - 1 := by
  -- by_cases hu : u ≤ 0
  -- · have hu' : ⌈u⌉ - 1 < 0 := by
  --     apply lt_of_lt_of_le
  --     linarith [ceil_lt_add_one u]
  --     apply ceil_le.2 hu
  --   rw [phi_eq_self_of_le_zero K L hu, sum_fiberwise_aux K L]
  --   symm
  --   by_cases huc : ⌈u⌉ < 0
  --   · have huc' : ⌈u⌉ - 1 < (-1) := by linarith [huc]
  --     simp only [Nat.card_eq_fintype_card, one_div, reduceNeg, huc', Finset.Icc_eq_empty_of_lt, sum_empty, zero_add, mul_comm, mul_assoc]

  --     sorry
  --   · have huc' : ⌈u⌉ = 0 := by omega
  --     have huc'' : ⌈u⌉ - 1 = (-1) := by linarith [huc']
  --     have hsum : ∑ s in Ramification_Group_diff K L (-1), i_[L/K]ₜ (u + 1) s = 0 := by
  --       apply Finset.sum_eq_zero
  --       intro x hx
  --       simp [truncatedLowerindex_eq_if K L (by linarith [huc'']) hx]
  --     simp [huc', huc'', hsum, mul_comm, mul_assoc, mul_inv_self]
  --     --sorry
  by_cases hc : 0 < u
  · have hu' : 0 ≤ ⌈u⌉ - 1 := by
      simp only [sub_nonneg, one_le_ceil_iff]; exact hc
        --push_neg at hu
        --simp [add_one_le_ceil_iff.2 hu, hu]
    calc
      _ = (1 / Nat.card G(L/K)_[0]) * ((∑ i in Finset.Icc 1 (⌈u⌉ - 1), Nat.card G(L/K)_[i]) + (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈u⌉])) := by
        apply phi_eq_sum_card K L hc
      _ = (1 / Nat.card G(L/K)_[0]) * ((∑ i in Finset.Icc 0 (⌈u⌉ - 1), Nat.card G(L/K)_[i]) + (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈u⌉])) - (1 : ℕ) := by
        have h : 0 < Nat.card G(L/K)_[0] := by rw [← ceil_zero (α := ℤ)]; sorry --apply Ramification_Group_card_pos
        erw [← sum_insert_left_aux 0 (⌈u⌉ - 1) hu' (fun x => Nat.card (lowerRamificationGroup K L x)), ← (Nat.div_self h), Nat.cast_div (by simp) (by simp [h]), ← (mul_one_div ((Nat.card G(L/K)_[0]) : ℚ) ((Nat.card G(L/K)_[0]) : ℚ)), (mul_comm ((Nat.card ↥ G(L/K)_[0]) : ℚ) (1 / ↑(Nat.card ↥ G(L/K)_[0] ))), ← mul_sub, Nat.cast_sub]
        · ring
        · rw [insert_Icc_left 0 (⌈u⌉ - 1) hu', Finset.sum_insert (by simp)]
          simp only [Nat.card_eq_fintype_card, zero_add, le_add_iff_nonneg_right, zero_le]
      _ = (1 / Nat.card G(L/K)_[0]) * ((∑ i in Finset.Icc (-1) (⌈u⌉ - 1), (i + 1) * (Nat.card G(L/K)_[i] - Nat.card G(L/K)_[(i + 1)])) + (u + 1) * (Nat.card G(L/K)_[⌈u⌉])) - 1 := by
        rw [sum_sub_aux K L hu', cast_sub]
        congr 2
        have h : (u - max 0 (⌈u⌉ - 1)) * (Nat.card G(L/K)_[⌈u⌉]) = (u + 1) * (Nat.card G(L/K)_[⌈u⌉]) - ⌈u⌉ * (Nat.card G(L/K)_[⌈u⌉]) := by
          simp only [hu', max_eq_right, cast_sub, cast_one, ← sub_add, Nat.card_eq_fintype_card]
          ring
        rw [h, add_sub, cast_mul, cast_natCast, add_comm_sub, add_sub]
        congr
      _ = (1 / Nat.card G(L/K)_[0]) * ((∑ i in Finset.Icc (-1) (⌈u⌉ - 1), ∑ s in Ramification_Group_diff K L i, (AlgEquiv.truncatedLowerIndex K L (u + 1) s)) + (u + 1) * (Nat.card G(L/K)_[⌈u⌉])) - 1 := by
        congr 3
        have h : Finset.Icc (-1) (⌈u⌉ - 1) = Finset.Icc (-1) (⌈u⌉ - 1) := by rfl
        rw [Int.cast_sum]
        apply sum_congr h
        intro x hx
        simp only [Nat.card_eq_fintype_card, cast_mul, cast_add, cast_one, cast_sub,
          Int.cast_natCast, (sum_of_diff_aux K L hx)]
      _ = (1 / Nat.card G(L/K)_[0]) * ((Finset.sum (⊤ : Finset (L ≃ₐ[K] L)) (AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) - 1 := by
        congr 2
        apply (sum_fiberwise_aux K L (u := u)).symm
  · have hu' : u = 0 := by apply (eq_of_le_of_not_lt hu hc).symm
    rw [hu', phi_zero_eq_zero]
    symm
    rw [sub_eq_zero, Raimification_Group_split K L 0, sum_union]
    · simp only [one_div, reduceNeg, zero_sub, Finset.Icc_self,
        disjiUnion_eq_biUnion, singleton_biUnion, zero_add]
      calc
        _ = ((Nat.card ↥ G(L/K)_[0]) : ℚ)⁻¹ * (0 + ∑ x ∈ (G(L/K)_[0] : Set (L ≃ₐ[K] L)).toFinset, i_[L/K]ₜ 1 x) := by
          -- congr
          simp only [Nat.card_eq_fintype_card, reduceNeg, zero_add, _root_.mul_eq_mul_left_iff, add_left_eq_self, inv_eq_zero, Nat.cast_eq_zero, Fintype.card_ne_zero, or_false]
          apply Finset.sum_eq_zero
          intro x hx
          rw [← zero_add 1, truncatedLowerindex_eq_if_aux K L (u := 0) (i := -1) rfl ?_ ?_ hx hgen]
          simp only [reduceNeg, cast_neg, cast_one, neg_add_cancel]
          rfl
          simp only [reduceNeg, ceil_zero, zero_sub, le_refl]
        _ = ((Nat.card ↥ G(L/K)_[0]) : ℚ)⁻¹ * (0 + Nat.card G(L/K)_[0]) := by
          congr
          have h : Nat.card G(L/K)_[0] = Finset.card (G(L/K)_[0] : Set (L ≃ₐ[K] L)).toFinset := by exact Nat.card_eq_card_toFinset  (G(L/K)_[0] : Set (L ≃ₐ[K] L))
          rw [h, Finset.cast_card]
          apply (Finset.sum_eq_sum_iff_of_le ?_).2
          <;> intro i hi
          · simp only [Set.mem_toFinset] at hi
            convert truncatedLowerIndex_aux K L 0 (by simp) i hi hgen
            repeat simp only [ceil_zero, cast_zero, zero_add]
          · simp only [Set.mem_toFinset] at hi
            apply le_of_eq; convert truncatedLowerIndex_aux K L 0 (by simp) i hi hgen
            repeat simp only [ceil_zero, cast_zero, zero_add]
        _ = 1 := by simp only [Nat.card_eq_fintype_card, zero_add, isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel]
    · unfold Ramification_Group_diff
      simp only [reduceNeg, zero_sub, Finset.Icc_self, toFinset_diff, disjiUnion_eq_biUnion, singleton_biUnion, neg_add_cancel]
      exact sdiff_disjoint
