import RamificationGroup.LowerNumbering
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.GroupTheory.Index
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Algebra.BigOperators.Basic

open DiscreteValuation Subgroup Set Function MeasureTheory Finset BigOperators Int Valued Eq

namespace HerbrandFunction

section

variable {G : Type*} [Group G] (H L K : Subgroup G)
-- `can be changed to use relindex`
noncomputable def _root_.Subgroup.relindex' : ℚ :=
  (K.index : ℚ) / (H.index: ℚ)

end

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [Algebra R S]


-- scoped notation:max  " φ_[" L:max "/" K:max "]" => phi K L

noncomputable def Index_of_G_i (u : ℚ) : ℚ :=
  if u > (-1) then
    relindex' G(S/R)_[0] G(S/R)_[(Int.ceil u)]
  else
    1

noncomputable def phi' (u : ℚ) : ℚ :=
  1 / (Index_of_G_i R S u)

noncomputable def phi (u : ℚ) :  ℚ :=
    if u ≥ 1 then
    ∑ x in Finset.Icc 1 (Int.floor u), (phi' R S x) + (u - (Int.floor u)) * (phi' R S u)
  else
    u * (phi' R S u)

--for mathlib
theorem sub_of_sum (a : ℤ) (f : ℚ → ℚ) (h : 1 ≤ a): ∑ x in Icc 1 (a + 1), f x - ∑ x in Icc 1 a, f x = f (a + 1) := by
  have hncons : (a + 1) ∉ Finset.Icc 1 a := by simp
  have hcons : (Finset.Icc 1 (a + 1)) = cons (a + 1) (Finset.Icc 1 a) hncons := by
    ext n
    simpa using (by omega)
  rw [hcons]
  rw [sum_cons]
  simp

--for mathlib
theorem ceil_eq_floor_add_one_iff (u : ℚ) (h : u ≠ ⌊u⌋) : ⌈u⌉ = ⌊u⌋ + 1 := by
  have hu : fract u ≠ 0 := by
    unfold fract
    by_contra h'
    have : u = ⌊u⌋ := by linarith [h']
    contradiction
  have h' : ⌈u⌉ = u + 1 - Int.fract u := by
    apply ceil_eq_add_one_sub_fract hu
  unfold fract at h'
  have h'': (⌈u⌉ : ℚ) = ((⌊u⌋ + 1) : ℚ):= by
    rw [h']
    ring
  exact_mod_cast h''

--for mathlib
theorem Int.eq_of_ge_of_lt_add_one (a m : ℤ) (h1 : m ≤ a) (h2 : a < (m + 1)) : a = m := by
  have hle : a ≤ m + 1 - 1 := by apply le_sub_one_iff.2 h2
  simp at hle
  apply ((LE.le.ge_iff_eq h1).1 hle).symm

theorem phi'_eq_ceil (u : ℚ) : phi' R S u = phi' R S ⌈u⌉ := by
  unfold phi' Index_of_G_i
  by_cases h : -1 < u
  · have hcl : ⌈u⌉ > (-1 : ℚ) := by
      apply lt_of_lt_of_le
      apply h
      apply le_ceil
    simp [h, hcl]
  have hcl : ¬⌈u⌉ > (-1 : ℚ) := by
    by_contra hc
    have hcl' : -1 < ⌈u⌉ := by apply cast_lt.1 hc
    have : -1 < u := by
      apply lt_ceil.1 hcl'
    contradiction
  simp [h, hcl]

theorem phi'_pos (u : ℚ) : 0 < phi' R S u := by
  unfold phi' Index_of_G_i relindex' index
  by_cases h : u > -1
  simp [h]
  apply div_pos_iff.2
  left
  constructor <;> sorry
  simp [h]

theorem phi'_neg_int_eq_one {u : ℤ} (hu : u ≤ 0) : phi' R S u = 1 := by
  unfold phi' Index_of_G_i
  by_cases hgt : (-1 : ℚ) < u
  · simp [hgt]
    have hzero : 0 = u := by
      have hgt' : -1 < u := by apply cast_lt.1 hgt
      have hge : -1 ≤ u - 1 := by
        apply le_sub_one_iff.2 hgt'
      simp at hge
      apply (LE.le.ge_iff_eq hge).1 hu
    have hzero' : u = (0 : ℚ) := by simp [hzero]
    sorry
  simp [hgt]

theorem phi_int_succ (a : ℤ) : (phi R S a) = (phi R S (a + 1)) - (phi' R S (a + 1)) := by
  unfold phi
  by_cases hgeone : (1 : ℚ) ≤ a
  · have hgezero : (0 : ℚ) ≤ a := by linarith
    simp [hgeone, hgezero]
    have h : ∑ x in Icc 1 (a + 1), phi' R S ↑x = phi' R S (a + 1) + ∑ x in Icc 1 a, phi' R S ↑x := by
      have hgeone' : 1 ≤ a := by apply cast_le.1 hgeone
      have h' : ∑ x in Finset.Icc 1 (a + 1), phi' R S ↑x - ∑ x in Finset.Icc 1 a, phi' R S ↑x = phi' R S (↑a + 1) := by
        apply sub_of_sum a (phi' R S) hgeone'
      linarith [h']
    simp [h]
  by_cases hgezero : (0 : ℚ) ≤ a
  · have heqzero : (0 : ℚ) = a := by
      --this
      push_neg at hgeone
      have hgeone' : a < 1 := by
        apply cast_lt.1 hgeone
      have hlezero  : a ≤ (0 : ℚ) := by
        convert le_sub_one_iff.2 hgeone'
        simp
      apply (LE.le.ge_iff_eq hgezero).1 hlezero
    erw [←heqzero]
    simp [hgeone, hgezero]
  simp [hgeone, hgezero]
  push_neg at *
  ring_nf
  apply mul_eq_mul_left_iff.2
  left
  rw [phi'_neg_int_eq_one]
  have : (1 + a) ≤ 0 := by
    have hgezero' : a < 0 := by apply cast_lt.1 hgezero
    have hle: a ≤ 0 - 1 := by
      convert le_sub_one_iff.2 hgezero'
    linarith [hle]
  symm
  convert phi'_neg_int_eq_one R S this
  simp
  apply le_of_lt
  apply cast_lt.1 hgezero

theorem phi_eq_self_of_le_neg_one {u : ℚ} (hu : u ≤ 0) : phi R S u = u := by
  unfold phi phi' Index_of_G_i relindex'
  have hu' : ¬u ≥ 1 := by linarith [hu]
  simp [hu']
  by_cases hu' : -1 < u
  <;> simp [hu']
  · have hu'' : ⌈u⌉ = 0 := by
      apply ceil_eq_iff.2
      constructor
      simp [hu']; simp [hu]
    simp [hu'']
    sorry

theorem phi_mono_int {a1 a2 : ℤ} (h : a1 < a2) : (phi R S a1) < (phi R S a2) := by
  have hsub : a2 = a1 + (a2 - a1 - 1) + 1 := by ring
  rw [hsub]
  induction' a2 - a1 - 1 with n ih
  · induction' n with n ih
    · apply sub_lt_zero.1
      rw [phi_int_succ R S a1]
      simp
      apply phi'_pos
    apply lt_trans
    apply ih
    simp
    apply sub_lt_zero.1
    have heq : phi R S (↑a1 + ↑n + 1) = phi R S (↑a1 + (↑n + 1) + 1) - (phi' R S (a1 + n + 1 + 1)) := by
      convert phi_int_succ R S (a1 + n + 1)
      <;>simp
      ring
    rw [heq]
    simp
    apply phi'_pos
  sorry

theorem phi_mono_int' (a1 a2 : ℤ) (h : a1 ≤ a2) : (phi R S a1) ≤ (phi R S a2) := by
  by_cases heq : a1 = a2
  simp [heq]
  apply le_of_lt
  push_neg at *
  have hlt : a1 < a2 := by apply lt_of_le_of_ne h heq
  apply phi_mono_int R S hlt

--i'll change this name
theorem phi_rational_floor (a : ℚ) : (phi R S a) = (phi R S ⌊a⌋) + ((phi R S (⌊a⌋ + 1)) - (phi R S ⌊a⌋)) * (a - ⌊a⌋) := by
  by_cases ha : a ≥ 1
  · unfold phi
    have hfl : (1 : ℚ) ≤ ⌊a⌋ := by
      convert le_floor.2 ha
      simp
      apply cast_le
    have hfl' : (0 : ℚ) ≤ ⌊a⌋ := by
      linarith [hfl]
    simp [ha, hfl, hfl']
    nth_rw 2 [mul_comm]
    apply mul_eq_mul_left_iff.2
    by_cases hzero : fract a = 0
    · right
      exact hzero
    left
    have h : ∑ x in Finset.Icc 1 (⌊a⌋ + 1), phi' R S ↑x - ∑ x in Finset.Icc 1 ⌊a⌋, phi' R S ↑x = phi' R S (⌊a⌋ + 1) := by
      have hfl' : (1 : ℤ) ≤ ⌊a⌋ := by apply cast_le.1 hfl
      apply sub_of_sum ⌊a⌋ (phi' R S) hfl'
    rw [h, phi'_eq_ceil]
    have hflcl : ⌈a⌉ = ⌊a⌋ + 1 := by
      unfold fract at hzero
      push_neg at hzero
      have : a ≠ ⌊a⌋ := by
        by_contra hc
        have hc' : a - ⌊a⌋ = 0 := by linarith
        contradiction
      apply ceil_eq_floor_add_one_iff a this
    rw [hflcl]
    congr
    simp
  have hfl : ¬ (1 : ℚ) ≤ ↑⌊a⌋ := by
    by_contra h'
    have h'' : (1 : ℚ) ≤ a := by
      apply le_floor.1
      convert h'
      simp
      apply cast_le.symm
    contradiction
  by_cases hzero : (0 : ℚ) ≤ ⌊a⌋
  · unfold phi
    simp [ha, hfl, hzero]
    push_neg at *
    --and this is the same
    have hflzero : 0 = ⌊a⌋ := by
      have hfl' : ⌊a⌋ < 1 := by apply cast_lt.1 hfl
      have hlezero : ⌊a⌋ ≤ 1 - 1 := by
        apply le_sub_one_iff.2 hfl'
      simp at hlezero
      have hgezero : 0 ≤ ⌊a⌋ := by apply cast_le.1 hzero
      apply (LE.le.ge_iff_eq hgezero).1 hlezero
    unfold fract
    simp [hflzero.symm]
    rw [mul_comm]
    apply mul_eq_mul_right_iff.2
    by_cases hzero' : a = 0
    · right
      exact hzero'
    left
    have hcl : ⌈a⌉ = 1 := by
      have hgtzero : (0 : ℚ) < a := by
        apply lt_of_le_of_ne
        have : ⌊a⌋ ≤ a := by apply floor_le
        apply le_trans
        apply hzero
        apply this
        push_neg at hzero'
        apply hzero'.symm
      apply ceil_eq_on_Ioc
      simp
      constructor
      apply hgtzero
      apply le_of_lt ha
    rw [phi'_eq_ceil, hcl]
    congr
  simp [ha, hfl, hzero]
  push_neg at *
  have ha' : a < 0 := by sorry
  rw [phi_eq_self_of_le_neg_one R S (by linarith [ha']), phi_eq_self_of_le_neg_one R S (by linarith [hzero])]
  sorry

theorem phi_rational_ceil (a : ℚ) : (phi R S a) = (phi R S (⌊a⌋ + 1)) - ((phi R S (⌊a⌋ + 1)) - (phi R S ⌊a⌋)) * (⌊a⌋ - a + 1) := by
  by_cases ha : (1 : ℚ) ≤ a
  · unfold phi
    have hfl : (1 : ℚ) ≤ ⌊a⌋ := by
      convert le_floor.2 ha
      apply cast_le
    have hcl : (1 : ℚ) ≤ (⌊a⌋ + 1) := by
      linarith [hfl]
    simp [ha, hcl, hfl]
    have h : ∑ x in Finset.Icc 1 (⌊a⌋ + 1), phi' R S ↑x - ∑ x in Finset.Icc 1 ⌊a⌋, phi' R S ↑x = phi' R S (⌊a⌋ + 1) := by
      have hfl' : (1 : ℤ) ≤ ⌊a⌋ := by apply cast_le.1 hfl
      apply sub_of_sum ⌊a⌋ (phi' R S) hfl'
    have h' :  (∑ x in Finset.Icc 1 (⌊a⌋ + 1), phi' R S ↑x - ∑ x in Finset.Icc 1 ⌊a⌋, phi' R S ↑x) - fract a * phi' R S a -
    (∑ x in Finset.Icc 1 (⌊a⌋ + 1), phi' R S ↑x - ∑ x in Finset.Icc 1 ⌊a⌋, phi' R S ↑x) * (↑⌊a⌋ - a + 1) = 0 := by
      rw [h]
      by_cases hfl' : a - ⌊a⌋ = 0
      · unfold fract
        have : ⌊a⌋ - a = 0 := by linarith [hcl]
        simp [hcl, this]
        left
        unfold fract
        linarith [this]
      push_neg at *
      have hcl' : (⌈a⌉ : ℚ) = (⌊a⌋ : ℚ) + 1:= by
        have hfl'' : a ≠ ⌊a⌋ := by
          by_contra hc
          have : a - ⌊a⌋ = 0 := by linarith [hc]
          contradiction
        have hcl'' : ⌈a⌉ = ⌊a⌋ + 1:= by
          apply ceil_eq_floor_add_one_iff a hfl''
        sorry
      ring_nf
      nth_rw 3 [phi'_eq_ceil]
      unfold fract
      have heq : phi' R S (1 + ⌊a⌋) = phi' R S ⌈a⌉ := by
        rw [hcl']
        have : 1 + (⌊a⌋ : ℚ) = (⌊a⌋ : ℚ) + 1 := by ring
        rw [this]
      rw [heq]
      ring
    linarith [h']
  have hfl : ¬(1 : ℚ) ≤ ⌊a⌋ := by
    by_contra hc
    have hge : (1 : ℚ) ≤ a := by
      apply le_floor.1
      convert hc
      simp
      apply cast_le.symm
    contradiction
  by_cases hcl : (1 : ℚ) ≤ (⌊a⌋ + 1)
  · unfold phi
    simp [ha, hcl, hfl]
    push_neg at *
    have hfl' : ⌊a⌋ = 0 := by
      simp at hcl
      have hfl' : ⌊a⌋ < 1 := by apply cast_lt.1 hfl
      apply Int.eq_of_ge_of_lt_add_one ⌊a⌋ 0 hcl hfl'
    simp [hfl']
    by_cases hzero : a = 0
    · simp [hzero]
    have h : phi' R S a = phi' R S 1 := by
      have h' : phi' R S a = phi' R S ⌈a⌉ := by
        apply phi'_eq_ceil
      rw [h']
      have hcl' : ⌈a⌉ = (1 : ℚ) := by
        have hnefl : a ≠ ⌊a⌋ := by
          rw [hfl']
          push_neg at hzero
          apply hzero
        have : ⌈a⌉ = ⌊a⌋ + 1 := by
          apply ceil_eq_floor_add_one_iff a hnefl
        rw [this]
        simp [hfl']
      rw [hcl']
    ring_nf
    simp [h]
  push_neg at *
  have hcl' : ⌊a⌋ < 0 := by sorry
  have ha' : a < 0 := by sorry
  simp [phi_eq_self_of_le_neg_one R S (by linarith [ha']), phi_eq_self_of_le_neg_one R S (by linarith [hcl'])]
  sorry

theorem phi_gt_floor : ∀ a : ℚ , (a ≠ ⌊a⌋) → (phi R S a) > (phi R S ⌊a⌋) := by
  rintro a ha
  apply gt_iff_lt.2
  apply sub_lt_zero.1
  nth_rw 2 [phi_rational_floor]
  simp
  apply mul_pos_iff.2
  left
  constructor
  simp
  convert phi_mono_int R S (show ⌊a⌋ < ⌊a⌋ + 1 by linarith)
  simp
  apply fract_pos.2 ha

theorem phi_lt_ceil : ∀ a : ℚ , (phi R S a) < (phi R S (⌊a⌋ + 1)) := by
  rintro a
  apply gt_iff_lt.2
  apply sub_lt_zero.1
  nth_rw 1 [phi_rational_ceil]
  simp
  apply mul_pos_iff.2
  left
  constructor
  simp
  convert phi_mono_int R S (show ⌊a⌋ < ⌊a⌋ + 1 by linarith)
  simp
  have h : a - 1 < ⌊a⌋ := by apply sub_one_lt_floor
  linarith [h]

theorem phi_mono_in_section : ∀ a1 a2 : ℚ , (⌊a1⌋ = ⌊a2⌋) ∧ (a1 < a2) → (phi R S a1) < (phi R S a2) := by
  rintro a1 a2 ⟨h1, h2⟩
  apply gt_iff_lt.2
  apply sub_lt_zero.1
  nth_rw 2 [phi_rational_floor]
  nth_rw 1 [phi_rational_floor]
  rw [h1]
  simp
  apply sub_lt_zero.1
  have : ((phi R S (↑⌊a2⌋ + 1)) - (phi R S ↑⌊a2⌋)) * (a1 - ↑⌊a2⌋) - ((phi R S (↑⌊a2⌋ + 1)) - (phi R S ↑⌊a2⌋)) * fract a2 = ((phi R S (↑⌊a2⌋ + 1)) - (phi R S ↑⌊a2⌋)) * (a1 - a2) := by
    unfold fract
    calc
      ((phi R S (↑⌊a2⌋ + 1)) - (phi R S ↑⌊a2⌋)) * (a1 - ↑⌊a2⌋) - ((phi R S (↑⌊a2⌋ + 1)) - (phi R S ↑⌊a2⌋)) * (a2 - ⌊a2⌋) = ((phi R S (↑⌊a2⌋ + 1)) - (phi R S ↑⌊a2⌋)) * ((a1 - ⌊a2⌋) - (a2 - ⌊a2⌋)) := by
        ring
      _ = ((phi R S (↑⌊a2⌋ + 1)) - (phi R S ↑⌊a2⌋)) * (a1 - a2) := by
        simp
        left
        unfold fract
        ring
  rw [this]
  apply mul_neg_iff.2
  left
  constructor
  simp
  convert phi_mono_int R S (show ⌊a2⌋ < ⌊a2⌋ + 1 by linarith)
  simp
  simp [h2]

--i'll change this name too
theorem phi_mono_over_section : ∀ a1 a2 : ℚ , (⌊a1⌋ ≠ ⌊a2⌋) ∧ (a1 < a2) → (phi R S a1) < (phi R S a2) := by
  rintro a1 a2 ⟨hne, hlt⟩
  by_cases hfloor : a2 = ⌊a2⌋
  have hle : ⌊a1⌋ + 1 ≤ ⌊a2⌋ := by
    have hlt : ⌊a1⌋ < ⌊a2⌋ := by
      apply lt_of_le_of_ne
      apply floor_le_floor
      apply le_of_lt hlt
      apply hne
    apply add_one_le_of_lt hlt
  apply lt_of_lt_of_le
  have h1 : (phi R S a1) < (phi R S (⌊a1⌋ + 1)) := by apply (phi_lt_ceil R S)
  apply h1
  have h2 : (phi R S (⌊a1⌋ + 1)) ≤ (phi R S a2) := by
    by_cases heq : (⌊a1⌋ + 1) = a2
    simp [heq]
    push_neg at heq
    have h1' : (phi R S (⌊a1⌋ + 1)) ≤ (phi R S ⌊a2⌋) := by
      convert phi_mono_int' R S (⌊a1⌋ + 1) ⌊a2⌋ hle
      simp
    rw [hfloor]
    exact h1'
  apply h2
  have hle : a1 ≤ ⌊a2⌋ := by
    by_contra hc
    push_neg at *
    have h : ⌊a1⌋ = ⌊a2⌋ := by
      have h1 : ⌊a1⌋ ≤ ⌊a2⌋ := by
        apply floor_le_floor
        apply le_of_lt
        exact hlt
      have h2 : ⌊a2⌋ ≤ ⌊a1⌋ := by
        apply le_floor.2
        apply le_of_lt hc
      apply (LE.le.ge_iff_eq h1).1 h2
    contradiction
  have hlt : ⌊a2⌋ < a2 := by
    have hge : ⌊a2⌋ ≤ a2 := by apply floor_le
    push_neg at hfloor
    apply lt_of_le_of_ne hge hfloor.symm
  apply lt_of_le_of_lt
  have h1 : (phi R S a1) ≤ (phi R S ⌊a2⌋) := by
    by_cases heq : a1 = ⌊a2⌋
    simp [heq]
    apply le_of_lt
    apply lt_of_lt_of_le
    push_neg at *
    have hlt' : a1 < ⌊a2⌋ := by apply lt_of_le_of_ne hle heq
    have h1' : (phi R S a1) < (phi R S (⌊a1⌋ + 1)) := by apply phi_lt_ceil R S
    apply h1'
    have hle' : ⌊a1⌋ + 1 ≤ ⌊a2⌋ := by
      push_neg at *
      have hlt' : ⌊a1⌋ < ⌊a2⌋ := by
        have hle'' : ⌊a1⌋ ≤ ⌊a2⌋ := by
          apply floor_le_floor
          apply le_of_lt
          assumption
        apply lt_of_le_of_ne hle'' hne
      apply Int.le_of_lt_add_one
      linarith [hlt']
    have h2' : (phi R S ↑(⌊a1⌋ + 1)) ≤ (phi R S (⌊a2⌋)) := by
      apply phi_mono_int' R S (⌊a1⌋ + 1) ⌊a2⌋ hle'
    convert h2'
    simp
  apply h1
  push_neg at hfloor
  have h2 : (phi R S ⌊a2⌋) < (phi R S a2) := by apply (phi_gt_floor R S a2 hfloor)
  apply h2

theorem phi_mono_iff : (∀a1 a2 : ℚ , a1 < a2 → (phi R S a1) < (phi R S a2)) ↔ (∀a1 a2 : ℤ , a1 < a2 → (phi R S a1) < (phi R S a2)) := by
  constructor
  rintro _ a1 a2
  apply phi_mono_int R S
  rintro _ a1 a2 h'
  by_cases hfloor : ⌊a1⌋ = ⌊a2⌋
  apply phi_mono_in_section
  constructor <;> assumption
  push_neg at *
  apply phi_mono_over_section
  constructor <;> assumption

theorem phi_strictMono : StrictMono (phi R S) := by
  rintro a1 a2
  revert a1 a2
  apply (phi_mono_iff R S).2
  apply phi_mono_int

theorem phi_bij : Function.Bijective (phi R S) := by
  constructor
  rintro a1 a2 h
  contrapose! h
  by_cases h1 : a1 > a2
  have hlt : (phi R S a2) < (phi R S a1) := by
    apply phi_strictMono
    apply h1
  apply ne_of_gt hlt
  have hlt : (phi R S a2) > (phi R S a1) := by
    apply phi_strictMono
    apply lt_of_not_ge
    push_neg at *
    exact lt_of_le_of_ne h1 h
  apply ne_of_lt hlt
  rintro b
  unfold phi phi'
  by_cases hb : b < 0
  sorry
  sorry

noncomputable def psi : ℚ → ℚ :=
  invFun (phi R S)

theorem psi_bij : Function.Bijective (psi R S) := by
  constructor
  have hpsi: (invFun (phi R S)).Injective :=
    (rightInverse_invFun (phi_bij R S).2).injective
  exact hpsi
  apply invFun_surjective
  apply (phi_bij R S).1

theorem phi_zero_eq_zero : phi R S 0 = 0 := by
  unfold phi
  simp

noncomputable def psi' (v : ℚ): ℚ :=
  1 / (phi' R S (psi R S v))

theorem psi_zero_eq_zero : psi R S 0 = 0 := by
  unfold psi
  nth_rw 1 [← phi_zero_eq_zero R S]
  have : id 0 = (0 : ℚ) := by rfl
  nth_rw 2 [← this]
  have Inj : (phi R S).Injective := by apply (phi_bij R S).1
  rw [← invFun_comp Inj]
  simp

theorem leftInverse_phi_psi : Function.LeftInverse (phi R S) (psi R S)  := by
  rintro a
  apply invFun_eq
  apply (phi_bij R S).surjective

@[simp]
theorem phi_psi_eq_self (u : ℚ) : (phi R S) ((psi R S) u) = u := leftInverse_phi_psi R S u


theorem psi_eq_self_of_le_neg_one {v : ℚ} (hv : v ≤ 0) : psi R S v = v := by
  have h1 : phi R S (psi R S v) = v := by apply phi_psi_eq_self
  have h2 : phi R S v = v := by apply phi_eq_self_of_le_neg_one R S hv
  apply (phi_bij R S).injective
  simp [h1, h2]

--lemma 3
open scoped Classical


variable (K L : Type*) {ΓK : outParam Type*} [Field K] [Field L] [LinearOrderedCommGroupWithZero ΓK] [vK : Valued K ΓK] [vS : Valued L ℤₘ₀] [Algebra K L] [FiniteDimensional K L]

noncomputable def G_diff (i : ℤ) : Finset (L ≃ₐ[K] L) := ((G(L/K)_[i] : Set (L ≃ₐ[K] L)) \ (G(L/K)_[(i + 1)] : Set (L ≃ₐ[K] L))).toFinset

theorem G_pairwiseDisjoint (n : ℤ) : (PairwiseDisjoint (↑(Finset.Icc (-1) (n - 1))) (G_diff K L)) := by
  induction' n with n ih
  induction' n with n ih
  simp
  sorry
  sorry

--i don't know how to name them
theorem x_in_G_n {x : (L ≃ₐ[K] L)} (hx : x ≠ .refl): ∃ (n : ℤ) , -1 ≤ n ∧ x ∈ G(L/K)_[n] ∧ x ∉ G(L/K)_[(n + 1)] := by
  by_contra hc
  push_neg at *
  sorry


theorem mem_all_lowerRamificationGroup_iff {x : (L ≃ₐ[K] L)}: (∀ n : ℤ, x ∈ G(L/K)_[n]) ↔ x = .refl := by
  constructor
  <;>rintro h
  have htop : i_[L/K] x = ⊤ := by
    by_contra hc
    simp at hc
    push_neg at *
    obtain ⟨m, hx, hx', hx''⟩ := x_in_G_n K L hc
    apply hx''
    apply h
  apply lowerIndex_eq_top_iff_eq_refl.1 htop
  rintro n
  have : x ∈ G(L/K)_[n.toNat] := by
    apply (mem_lowerRamificationGroup_iff n.toNat).2
    rw [h, (lowerIndex_refl (R := K) (S := L))]
    simp
  sorry



theorem m_lt_n_of_in_G_m_of_notin_G_n {x : (L ≃ₐ[K] L)} {m n : ℤ} (hm : x ∈ G(L/K)_[m]) (hn : x ∉ G(L/K)_[n]) : m ≤ n - 1 := by
  by_contra hc
  push_neg at *
  have h : G(L/K)_[m] ≤  G(L/K)_[n] := by
    convert lowerRamificationGroup.antitone K L hc
    simp
  sorry

theorem G_n_or_G_lt_n {n : ℤ} {x : (L ≃ₐ[K] L)} (h : x ∉ G(L/K)_[n]) : ∃ a, (-1 ≤ a ∧ a ≤ n - 1) ∧ x ∈ G_diff K L a := by
  have hx : x ≠ .refl := by
    by_contra hc
    have : x ∈ G(L/K)_[n] := by apply (mem_all_lowerRamificationGroup_iff K L).2 hc
    contradiction
  obtain ⟨m, ⟨hmgt, hx, hx'⟩⟩ := (x_in_G_n K L hx)
  have hm' : m ≤ n - 1 := by apply m_lt_n_of_in_G_m_of_notin_G_n K L hx h
  have hx'' : x ∈ G_diff K L m := by simp [G_diff, hx, hx']
  use m

theorem G_split (n : ℤ) : (⊤ : Finset (L ≃ₐ[K] L)) = (disjiUnion (Finset.Icc (-1) (n - 1)) (G_diff K L) (G_pairwiseDisjoint K L n)) ∪ (G(L/K)_[n] : Set (L ≃ₐ[K] L)).toFinset := by
  ext x
  constructor
  simp
  by_cases h : x ∈ G(L/K)_[n]
  · right
    assumption
  left
  apply G_n_or_G_lt_n K L h
  simp

theorem Sum_Trunc_lower_Index_of_G_n (n : ℤ) (u : ℚ) (h : u ≤ n) : (Finset.sum (G(L/K)_[n] : Set (L ≃ₐ[K] L)).toFinset ((AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) = (u + 1) * (Nat.card (G(L/K)_[n])) := by
  calc
  _ = Finset.sum (G(L/K)_[n] : Set (L ≃ₐ[K] L)).toFinset (fun (x : _) => u + 1) := by
    apply sum_equiv (.refl (L ≃ₐ[K] L))
    simp
    rintro s hs
    sorry
  _ = (u + 1) * (Nat.card (G(L/K)_[n])) := by
    norm_num
    ring

theorem Sum_Trunc_lower_Index_of_diff_G (n : ℤ) (u : ℚ) (h : n ≤ u) : (Finset.sum (G_diff K L n) ((AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) = (n + 1) * (Nat.card (G_diff K L n)) := by
  calc
  _ = (Finset.sum (G_diff K L n) (fun (x : _) => ((n : ℚ) + 1))) := by
    apply sum_equiv (.refl (L ≃ₐ[K] L))
    simp
    rintro s hs
    sorry
  _ = (n + 1) * (Nat.card (G_diff K L n)) := by
    norm_num
    ring

theorem phi_eq_Sum_Inf (u : ℚ) : (phi K L u) = (1 / Nat.card G(L/K)_[0]) * ((Finset.sum (⊤ : Finset (L ≃ₐ[K] L)) (AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) - 1 := by
  by_cases h : u ≥ 1
  · simp [h]
    have hsplit : (Finset.sum (⊤ : Finset (L ≃ₐ[K] L)) (AlgEquiv.truncatedLowerIndex K L (u + 1) ·)) = (Finset.sum (((disjiUnion (Finset.Icc (-1) (⌈u⌉ - 1)) (G_diff K L) (G_pairwiseDisjoint K L _)))) ((AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) + (Finset.sum (((G(L/K)_[(⌈u⌉)] : Set (L ≃ₐ[K] L)).toFinset)) ((AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) := by
      calc
      _ = (Finset.sum (((disjiUnion (Finset.Icc (-1) (⌈u⌉ - 1)) (G_diff K L) (G_pairwiseDisjoint K L _)) ∪ (G(L/K)_[(⌈u⌉)] : Set (L ≃ₐ[K] L)).toFinset)) ((AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) := by
        congr
        apply G_split
      _ = (Finset.sum (((disjiUnion (Finset.Icc (-1) (⌈u⌉ - 1)) (G_diff K L) (G_pairwiseDisjoint K L _)))) ((AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) + (Finset.sum (((G(L/K)_[(⌈u⌉)] : Set (L ≃ₐ[K] L)).toFinset)) ((AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) := by
        have : Disjoint (disjiUnion (Finset.Icc (-1) (⌈u⌉ - 1)) (G_diff K L) (G_pairwiseDisjoint K L _)) (toFinset ↑ G(L/K)_[⌈u⌉]) := by sorry
        apply sum_union
        apply this
    have hsplit' : (Finset.sum (((disjiUnion (Finset.Icc (-1) (⌈u⌉ - 1)) (G_diff K L) (G_pairwiseDisjoint K L _)))) ((AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) = Finset.sum _ fun (i : ℤ) => Finset.sum _ fun (x : _) => (AlgEquiv.truncatedLowerIndex K L (u + 1) x) := by
      apply sum_disjiUnion
    simp at hsplit hsplit'
    rw [hsplit, hsplit']
    have hu : (Finset.sum ((G(L/K)_[(⌈u⌉)] : Set (L ≃ₐ[K] L)).toFinset) ((AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) = (u + 1) * (Nat.card G(L/K)_[⌈u⌉]) := by
      convert Sum_Trunc_lower_Index_of_G_n K L ⌈u⌉ u (by apply le_ceil)
    rw [hu]
    have hd : Finset.sum (Finset.Icc (-1) (⌈u⌉ - 1)) (fun (i : ℤ) => Finset.sum (G_diff K L i) (fun (x : _) => (AlgEquiv.truncatedLowerIndex K L (u + 1) x))) = Finset.sum (Finset.Icc (-1) (⌈u⌉ - 1)) fun (i : ℤ) => (i + 1) * (Nat.card ((G(L/K)_[i] : Set (L ≃ₐ[K] L)) \ G(L/K)_[(i + 1)] : Set (L ≃ₐ[K] L))):= by
      norm_num
      apply sum_equiv (.refl ℤ)
      simp
      simp
      rintro i hge hle
      have hle' : i ≤ u := by
        sorry
      convert Sum_Trunc_lower_Index_of_diff_G K L i u hle'
      unfold G_diff
      simp
      sorry
    rw [hd]
    sorry
  unfold phi
  simp [h]
  sorry

-- scoped notation:max  " ψ_[" L:max "/" K:max "]" => psi K L

end HerbrandFunction
