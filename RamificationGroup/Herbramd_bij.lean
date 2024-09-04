import RamificationGroup.Herbrand_aux
import Mathlib.RingTheory.Valuation.Basic

open scoped Classical
open HerbrandFunction DiscreteValuation AlgEquiv Valued
open DiscreteValuation Subgroup Set Function Finset BigOperators Int Valued

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [vK : Valued K ℤₘ₀] [Valuation.IsDiscrete vK.v] [vL : Valued L ℤₘ₀] [Algebra K L] [IsValExtension K L] [FiniteDimensional K L] [CompleteSpace K] [Algebra.IsSeparable K L]
[Algebra.IsSeparable (LocalRing.ResidueField ↥𝒪[K]) (LocalRing.ResidueField ↥𝒪[L])]

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [Algebra R S]

theorem sum_insert_right_aux''' (a b : ℤ) (h : a ≤ b) (f : ℤ → ℕ) : (∑ x in Finset.Icc a b, f x) = (∑ x in Finset.Icc a (b - 1), f x) + f b := by
  calc
    _ = ∑ x in insert b (Finset.Icc a (b - 1)), f x := by
      rw [insert_Icc_right _ _ h]
    _ = (∑ x in Finset.Icc a (b - 1), f x) + f b := by simp [add_comm]

theorem aux_1 {n : ℤ} (hn : 1 ≤ n): (∑ x ∈ Finset.Icc 1 (⌈(n : ℚ) + 1⌉ - 1), Nat.card G(L/K)_[x]) - (∑ x ∈ Finset.Icc 1 (⌈(n : ℚ)⌉ - 1), Nat.card G(L/K)_[x]) = (Nat.card G(L/K)_[n]) := by
  simp only [ceil_add_one, ceil_intCast, add_sub_cancel_right]
  rw [sum_insert_right_aux''' 1 n hn (fun x => (Nat.card G(L/K)_[x]))]
  simp only [Nat.card_eq_fintype_card, add_tsub_cancel_left]


#check Nat.Icc_insert_succ_right
theorem phi_linear_section_aux {n : ℤ} {x : ℚ} (hx : n ≤ x ∧ x < n + 1) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : phi K L x = phi K L n + (phi K L (n + 1) - phi K L n) * (x - n) := by
  by_cases hc : 0 < x
  · have hn : (0 : ℚ) ≤ n := by
      by_contra hcon
      push_neg at hcon
      rw [← add_lt_add_iff_right 1, zero_add, ← Int.cast_one, ← cast_add, cast_lt] at hcon
      have hcon' : n + 1 ≤ 0 := by
        apply Int.le_sub_one_of_lt hcon
      have hx : x < 0 := by
        apply lt_of_lt_of_le hx.2
        rw [← Int.cast_one (R := ℚ), ← cast_add, ← cast_zero, cast_le]
        exact hcon'
      absurd hc; linarith [hx]
    by_cases hc' : (0 : ℚ) < n
    · rw [phi_eq_sum_card K L hc]
      nth_rw 1 [phi_eq_sum_card K L hc']
      by_cases hc'' : ⌈x⌉ = ⌈(n : ℚ)⌉
      -- · rw [hc'', mul_add, mul_add, add_assoc]
      --   congr
      · have hx' : x = n := by
          by_contra hcon
          rw [ceil_intCast] at hc''
          have ceil_lt := hc'' ▸ (lt_of_le_of_ne hx.left (fun eq => hcon eq.symm))
          linarith [Int.le_ceil x]
        simp only [hx', sub_self, mul_zero, add_zero]
        --rw [phi_eq_sum_card K L, phi_eq_sum_card K L]
         -- exact hc'
        -- linarith [hc']
      · have hx' : ⌈x⌉ = ⌈(n : ℚ) + 1⌉ := by
          apply Int.ceil_eq_iff.mpr
          simp
          exact ⟨lt_of_le_of_ne hx.left (fun eq => hc'' (by congr; exact eq.symm)), le_of_lt hx.right⟩
        simp only [hx']
        rw [← sub_eq_iff_eq_add', ← mul_sub, ← sub_sub, add_comm, ← add_sub, add_comm, ← add_sub]
        calc
          _ = (1 / Nat.card G(L/K)_[0]) * ((Nat.card G(L/K)_[n]) +  ((x - (max 0 (⌈(n : ℚ) + 1⌉ - 1))) * (Nat.card G(L/K)_[⌈(n : ℚ) + 1⌉] ) - (n - (max 0 (⌈(n : ℚ)⌉ - 1))) * (Nat.card G(L/K)_[⌈(n : ℚ)⌉] ))) := by
            rw [← Nat.cast_sub, aux_1 K L (n := n)]
            apply Int.le_of_sub_one_lt
            rw [sub_self]
            apply_mod_cast hc'
            apply sum_le_sum_of_subset_of_nonneg
            refine Finset.Icc_subset_Icc (by linarith) ?_
            simp only [ceil_intCast, ceil_add_one, add_sub_cancel_right, tsub_le_iff_right,le_add_iff_nonneg_right, zero_le_one]
            intro i hi1 hi2
            apply le_of_lt
            convert Ramification_Group_card_pos K L (u := i)
            exact Eq.symm (ceil_intCast i)
          _ = (1 / Nat.card G(L/K)_[0]) * (Nat.card G(L/K)_[(n + 1)]) * (x - n) := by
            simp only [ceil_add_one, ceil_intCast, add_sub_cancel_right, cast_max, cast_zero, cast_sub, cast_one, max_eq_right hn]
            have hn' : 0 ≤ (n : ℚ) - 1 := by
              rw [← cast_zero, ← cast_one, ← cast_sub, cast_le]
              apply Int.le_sub_one_of_lt
              apply_mod_cast hc'
            simp only [Nat.card_eq_fintype_card, one_div, max_eq_right hn', sub_sub_cancel, one_mul,add_sub_cancel]
            ring
          _ = _ := by
            congr
            repeat rw [phi_eq_sum_card K L]
            simp only [ceil_add_one, ceil_intCast, add_sub_cancel_right, Nat.cast_sum, cast_max, cast_zero, cast_sub, cast_one]
            rw [← mul_sub]
            congr
            have aux₁: max 0 (n : ℚ) = n := by
              apply max_eq_right
              apply le_of_lt hc'
            have aux₂: max 0 (n - 1 : ℚ) = n - 1 := by
              apply max_eq_right
              rw [← cast_zero, ← cast_one, ← cast_sub, cast_le]
              apply Int.le_sub_one_of_lt
              apply_mod_cast hc'
            rw [aux₁, aux₂, ← sum_insert_right_aux'' 1 n ?_ (fun x => (Nat.card G(L/K)_[x] : ℚ))]
            simp only [Nat.card_eq_fintype_card, add_sub_cancel_left, one_mul, sub_sub_cancel, sub_add_cancel]
            apply Int.le_of_sub_one_lt
            simp only [sub_self]
            apply_mod_cast hc'
            exact hc'
            linarith [hc']
            -- conv =>
            --   enter [2, 1, 1, 1]
            --   rw [show n = n - 1 + 1 by simp]
    · have hn' : n = 0 := by
        symm
        apply eq_of_le_of_not_lt
        apply_mod_cast hn
        apply_mod_cast hc'
      simp only [hn', cast_zero, zero_add, sub_zero]
      rw [phi_zero_eq_zero]; ring
      simp only [hn', cast_zero, zero_add] at hx
      rw [phi_of_pos_of_le_one K L hc (by apply le_of_lt hx.2), mul_comm, _root_.mul_eq_mul_right_iff]; left
      unfold phi
      simp only [ceil_one, sub_self, zero_lt_one, Finset.Icc_eq_empty_of_lt, sum_empty, max_self, cast_zero, sub_zero, one_mul, zero_add]
      convert phiDeriv_eq_ceil K L; symm; simp only [cast_eq_one]
      apply Int.ceil_eq_iff.2
      constructor
      · simp only [cast_one, sub_self, hc]
      · apply le_of_lt; simp only [cast_one, hx.2]
  · push_neg at hc
    rw [phi_eq_self_of_le_zero K L hc]
    by_cases hc' : x = 0
    · have hn : n = 0 := by
        apply eq_of_le_of_not_lt
        · rw [hc'] at hx
          apply_mod_cast hx.1
        · rw [hc'] at hx; push_neg
          rw [← add_zero n]
          nth_rw 2 [← sub_self 1]
          rw [add_sub]
          apply Int.le_sub_one_of_lt (a := 0) (b := n + 1)
          apply_mod_cast hx.2
      rw [hn, cast_zero, phi_zero_eq_zero K L, zero_add, zero_add, hc']; ring
    · have hn : ((n : ℚ) + 1) ≤ 0 := by
        rw [← cast_one, ← cast_add, ← cast_zero, cast_le, ← sub_self 1]
        apply Int.le_sub_one_of_lt
        simp only [add_lt_iff_neg_right]
        rw [← cast_lt (R := ℚ)]
        apply lt_of_le_of_lt (b := x)
        exact hx.1
        apply lt_of_le_of_ne hc hc'
      have hn' : (n : ℚ) ≤ 0 := by linarith [hn]
      rw [phi_eq_self_of_le_zero K L hn, phi_eq_self_of_le_zero K L hn']; ring

theorem phi_Bijective_section_aux {n : ℤ} {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : ∀ (y : ℚ) , (phi K L n) ≤ y ∧ y < (phi K L (n + 1)) → ∃ (x : ℚ), phi K L x = y := by
  intro y ⟨hy1, hy2⟩
  use (n + ((y - phi K L n) / (phi K L (n + 1) - phi K L n)))
  have hx : n ≤ (n + ((y - phi K L n) / (phi K L (n + 1) - phi K L n))) ∧ (n + ((y - phi K L n) / (phi K L (n + 1) - phi K L n))) < n + 1 := by
    constructor
    · simp only [le_add_iff_nonneg_right]
      apply div_nonneg
      · simp only [sub_nonneg, hy1]
      · apply le_of_lt
        simp only [sub_pos]
        apply phi_strictMono
        linarith
    · simp only [add_lt_add_iff_left]
      apply (div_lt_one ?_).2
      · simp only [sub_lt_sub_iff_right, hy2]
      · simp only [sub_pos]
        apply phi_strictMono
        linarith
  rw [phi_linear_section_aux K L hx hgen]
  rw [add_comm (n : ℚ) ((y - phi K L n) / (phi K L (n + 1) - phi K L n)), add_sub_assoc, sub_self, add_zero, div_eq_inv_mul, ← mul_assoc, Rat.mul_inv_cancel, one_mul, add_sub_cancel]
  -- have :  (phi K L (↑n + 1) - phi K L ↑n) * ((y - phi K L ↑n) / (phi K L (↑n + 1) - phi K L ↑n)) = (y - phi K L n) := by
  --   rw [div_eq_inv_mul, ← mul_assoc, Rat.mul_inv_cancel, one_mul]
  apply sub_ne_zero_of_ne
  apply ne_of_gt
  apply phi_strictMono
  linarith

theorem card_of_Ramigroup_gt_one {n : ℤ} : 1 ≤ Nat.card G(L/K)_[n] := by
  refine Nat.one_le_iff_ne_zero.mpr ?_
  apply ne_of_gt
  convert Ramification_Group_card_pos K L (u := n)
  exact Eq.symm (ceil_intCast n)

theorem id_le_phi {x : ℚ} (hx : 0 < x) : (1 / Nat.card G(L/K)_[0]) * x ≤ phi K L x := by
  rw [phi_eq_sum_card K L hx]
  apply le_trans (b := 1 / (Nat.card ↥ G(L/K)_[0]) * ((∑ x ∈ Finset.Icc 1 (⌈x⌉ - 1), (1 : ℕ)) + (x - (max 0 (⌈x⌉ - 1))) * (Nat.card G(L/K)_[⌈x⌉] )))
  · rw [← Finset.cast_card]
    apply le_trans (b :=  1 / ↑(Nat.card ↥ G(L/K)_[0] ) * (↑↑(Finset.Icc 1 (⌈x⌉ - 1)).card + (x - ↑(max 0 (⌈x⌉ - 1))) * 1))
    · rw [mul_one, mul_le_mul_iff_of_pos_left]
      have hxc : 0 ≤ ⌈x⌉ - 1 := by
        linarith [Int.one_le_ceil_iff.2 hx]
      simp only [card_Icc, sub_add_cancel, pred_toNat, hxc, max_eq_right, cast_sub, cast_one, ge_iff_le]
      rw [Nat.cast_sub, ← Int.cast_natCast, Int.toNat_of_nonneg]
      ring; rfl
      linarith [hxc]
      rw [← Nat.cast_le (α := ℤ), Int.toNat_of_nonneg, Nat.cast_one]
      <;> linarith [hxc]
      simp only [one_div, inv_pos, Nat.cast_pos]
      apply Ramification_Group_card_pos K L (u := 0)
    · apply (mul_le_mul_left ?_).2
      apply Rat.add_le_add_left.2
      apply (mul_le_mul_left ?_).2
      rw [← Nat.cast_one, Nat.cast_le]
      apply card_of_Ramigroup_gt_one
      simp only [cast_max, cast_zero, cast_sub, cast_one, sub_pos, max_lt_iff]
      constructor
      · exact hx
      · linarith [Int.ceil_lt_add_one x]
      refine one_div_pos.mpr ?_
      simp only [Nat.cast_pos]
      apply Ramification_Group_card_pos K L (u := 0)
  · apply (mul_le_mul_left ?_).2
    rw [add_le_add_iff_right, Nat.cast_le]
    apply Finset.sum_le_sum
    intro i hi
    apply card_of_Ramigroup_gt_one
    refine one_div_pos.mpr ?_
    simp only [Nat.cast_pos]
    apply Ramification_Group_card_pos K L (u := 0)

theorem phi_infty_up_aux {x : ℚ} : ∃ y, x ≤ phi K L y := by
  by_cases hc : 0 < x
  · use (Nat.card G(L/K)_[0]) * x
    apply le_trans (b := (1 / Nat.card G(L/K)_[0]) * (Nat.card G(L/K)_[0]) * x)
    · simp only [Nat.card_eq_fintype_card, one_div, isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel, one_mul, le_refl]
    · rw [mul_assoc]
      apply id_le_phi K L (x := (Nat.card G(L/K)_[0]) * x)
      apply mul_pos
      rw [Nat.cast_pos]
      convert Ramification_Group_card_pos K L (u := 0)
      exact hc
  · use x; push_neg at hc
    rw [phi_eq_self_of_le_zero K L hc]

theorem phi_infty_down_aux {y : ℚ} : ∃ x, phi K L x ≤ y := by
  by_cases hc : 0 ≤ y
  · use 0
    rw [phi_zero_eq_zero]
    exact hc
  · use y
    rw [phi_eq_self_of_le_zero]
    linarith [hc]

theorem phi_infty_aux (y : ℚ) : ∃ n : ℤ, phi K L n ≤ y ∧ y < phi K L (n + 1) := by
  by_contra hc
  push_neg at hc
  have hz : ∀ n : ℤ, phi K L n ≤ y := by
    intro n
    have h1 : ∃ n₀ : ℤ, phi K L n₀ ≤ y := by
      obtain ⟨n₀, hn₀⟩ := phi_infty_down_aux  K L (y := y)
      use ⌊n₀⌋
      apply le_trans (b := phi K L n₀)
      · apply StrictMono.monotone (phi_strictMono K L)
        exact floor_le n₀
      · exact hn₀
    obtain ⟨n₀, hn₀⟩ := h1
    have h2 : ∀ t : ℤ, t < n₀ → phi K L t ≤ y := by
      intro t ht
      apply le_of_lt
      apply lt_of_lt_of_le (b := phi K L n₀)
      apply phi_strictMono
      simp only [cast_lt, ht]
      exact hn₀
    have h3 : ∀ t : ℤ, n₀ < t → phi K L t ≤ y := by
      intro t ht
      have h : ∃ i : ℕ, t = n₀ + i := by
        use (t - n₀).toNat
        rw [Int.toNat_of_nonneg]
        ring
        apply le_of_lt
        linarith
      obtain ⟨i, hi⟩ := h
      rw [hi] at *
      induction' i with x hx
      simp only [CharP.cast_eq_zero, add_zero, hn₀]
      convert hc (n₀ + x) (hx ?_)
      · push_cast
        rw [add_assoc]
      · rfl
    by_cases hc : n = n₀
    · rw [hc]; exact hn₀
    · by_cases hc' : n < n₀
      · exact h2 n hc'
      · have hn : n₀ < n := by
          by_contra hcon
          apply hc
          push_neg at *
          exact Int.le_antisymm hcon hc'
        exact h3 n hn
  have hq : ∀ n : ℚ, phi K L n ≤ y := by
    intro n
    apply le_trans (b := phi K L ⌈n⌉)
    · by_cases hc : n = ⌈n⌉
      · rw [← hc]
      · apply le_of_lt; apply phi_strictMono K L _
        apply lt_of_le_of_ne; apply Int.le_ceil; exact hc
    · apply hz ⌈n⌉
  absurd hq; push_neg;
  obtain ⟨n, hn⟩ := phi_infty_up_aux K L (x := y)
  use n + 1
  apply lt_of_le_of_lt (b := phi K L n)
  exact hn
  apply phi_strictMono
  linarith

theorem phi_Bijective_aux {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : Function.Bijective (phi K L) := by
  constructor
  · rintro a1 a2 h
    contrapose! h
    by_cases h1 : a1 > a2
    · apply ne_of_gt (phi_strictMono K L h1)
    · push_neg at *
      apply ne_of_lt (phi_strictMono K L (lt_of_le_of_ne h1 h))
  · rintro y
    obtain ⟨n, hn⟩ := phi_infty_aux K L y
    apply phi_Bijective_section_aux K L (n := n) hgen y hn
