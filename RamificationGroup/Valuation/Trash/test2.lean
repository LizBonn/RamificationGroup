import RamificationGroup.LowerNumbering
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import RamificationGroup.Unused.MissingPiecesOfMathlib
import Mathlib.GroupTheory.Index
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Algebra.BigOperators.Basic

--definition of varphi and psi

open DiscreteValuation Subgroup Set Function MeasureTheory Finset BigOperators Int

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [ValAlgebra R S]

noncomputable def Index_of_G_i (u : ℚ) : ℚ :=
  if u ≥ (-1) then
    relindex' G(S/R)_[0] G(S/R)_[(Int.ceil u)]
  else
    1

noncomputable def varphi' (u : ℚ) : ℚ :=
  1 / (Index_of_G_i R S u)

noncomputable def varphi (u : ℚ) : ℚ :=
  if u ≥ 1 then
    ∑ x in Finset.Icc 1 (Int.floor u), (varphi' R S x) + (u - (Int.floor u)) * (varphi' R S u)
  else
    u * (varphi' R S u)

theorem varphi'_pos : ∀ u : ℚ , 0 < varphi' R S u := by
  unfold varphi' Index_of_G_i relindex' index
  rintro u
  by_cases h : u ≥ -1
  simp [h]
  apply div_pos_iff.2
  left
  constructor <;> sorry
  simp [h]

theorem varphi_int_succ : ∀a : ℤ , (varphi R S a) = (varphi R S (a + 1)) - (varphi' R S (a + 1)) := by
  rintro a
  unfold varphi
  by_cases hgeone : (1 : ℚ) ≤ a
  · have hgezero : (0 : ℚ) ≤ a := by linarith
    simp [hgeone, hgezero]
    sorry
  by_cases hgezero : (0 : ℚ) ≤ a
  · have heqzero : (0 : ℚ) = a := by
      sorry
    erw [←heqzero]
    simp [hgeone, hgezero]
  simp [hgeone, hgezero]
  sorry

theorem varphi_mono_int : ∀a1 a2 : ℤ , a1 < a2 → (varphi R S a1) < (varphi R S a2) := by
  rintro a1 a2 h
  have hsub : a2 = a1 + (a2 - a1 - 1) + 1 := by ring
  rw [hsub]
  induction' a2 - a1 - 1 with n ih
  · induction' n with n ih
    · apply sub_lt_zero.1
      rw [varphi_int_succ R S a1]
      simp
      apply varphi'_pos
    apply lt_trans
    apply ih
    simp
    apply sub_lt_zero.1
    have heq : varphi R S (↑a1 + ↑n + 1) = varphi R S (↑a1 + (↑n + 1) + 1) - (varphi' R S (a1 + n + 1 + 1)) := by
      convert varphi_int_succ R S (a1 + n + 1)
      <;>simp
      ring
    rw [heq]
    simp
    apply varphi'_pos
  sorry

theorem varphi_mono_int' : ∀a1 a2 : ℤ , a1 ≤ a2 → (varphi R S a1) ≤ (varphi R S a2) := by
  rintro a1 a2 h
  by_cases heq : a1 = a2
  simp [heq]
  apply le_of_lt
  push_neg at *
  have hlt : a1 < a2 := by apply lt_of_le_of_ne h heq
  apply varphi_mono_int R S a1 a2 hlt

--i'll change this name
theorem varphi_rational_floor : ∀ a : ℚ , (varphi R S a) = (varphi R S ⌊a⌋) + ((varphi R S (⌊a⌋ + 1)) - (varphi R S ⌊a⌋)) * (a - ⌊a⌋) := by
  rintro a
  unfold varphi
  by_cases ha : a ≥ 1
  · have hfl : (1 : ℚ) ≤ ⌊a⌋ := by
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
    sorry
  have hfl : ¬ (1 : ℚ) ≤ ↑⌊a⌋ := by
    by_contra h'
    have h'' : (1 : ℚ) ≤ a := by
      apply le_floor.1
      convert h'
      simp
      apply cast_le.symm
    contradiction
  by_cases hzero : (0 : ℚ) ≤ ⌊a⌋
  · simp [ha, hfl, hzero]
    sorry
  simp [ha, hfl, hzero]
  sorry


theorem varphi_rational_ceil : ∀ a : ℚ , (varphi R S a) = (varphi R S (⌊a⌋ + 1)) - ((varphi R S (⌊a⌋ + 1)) - (varphi R S ⌊a⌋)) * (⌊a⌋ - a + 1) := by
  rintro a
  unfold varphi
  by_cases ha : (1 : ℚ) ≤ a
  · have hfl : (1 : ℚ) ≤ ⌊a⌋ := by
      convert le_floor.2 ha
      apply cast_le
    have hcl' : (1 : ℚ) ≤ (⌊a⌋ + 1) := by
      linarith [hfl]
    simp [ha, hcl', hfl]
    sorry
  have hfl : ¬(1 : ℚ) ≤ ⌊a⌋ := by
    by_contra hc
    have hge : (1 : ℚ) ≤ a := by
      apply le_floor.1
      convert hc
      simp
      apply cast_le.symm
    contradiction
  by_cases hcl : (1 : ℚ) ≤ (⌊a⌋ + 1)
  · simp [ha, hcl, hfl]
    sorry
  simp [ha, hcl, hfl]
  sorry

theorem varphi_gt_floor : ∀ a : ℚ , (a ≠ ⌊a⌋) → (varphi R S a) > (varphi R S ⌊a⌋) := by
  rintro a ha
  apply gt_iff_lt.2
  apply sub_lt_zero.1
  nth_rw 2 [varphi_rational_floor]
  simp
  apply mul_pos_iff.2
  left
  constructor
  simp
  convert varphi_mono_int R S ⌊a⌋ (⌊a⌋ + 1) (by simp)
  simp
  apply fract_pos.2 ha

theorem varphi_lt_ceil : ∀ a : ℚ , (varphi R S a) < (varphi R S (⌊a⌋ + 1)) := by
  rintro a
  apply gt_iff_lt.2
  apply sub_lt_zero.1
  nth_rw 1 [varphi_rational_ceil]
  simp
  apply mul_pos_iff.2
  left
  constructor
  simp
  convert varphi_mono_int R S ⌊a⌋ (⌊a⌋ + 1) (by simp)
  simp
  have h : a - 1 < ⌊a⌋ := by apply sub_one_lt_floor
  linarith [h]

theorem varphi_mono_in_section : ∀ a1 a2 : ℚ , (⌊a1⌋ = ⌊a2⌋) ∧ (a1 < a2) → (varphi R S a1) < (varphi R S a2) := by
  rintro a1 a2 ⟨h1, h2⟩
  apply gt_iff_lt.2
  apply sub_lt_zero.1
  nth_rw 2 [varphi_rational_floor]
  nth_rw 1 [varphi_rational_floor]
  rw [h1]
  simp
  apply sub_lt_zero.1
  have : ((varphi R S (↑⌊a2⌋ + 1)) - (varphi R S ↑⌊a2⌋)) * (a1 - ↑⌊a2⌋) - ((varphi R S (↑⌊a2⌋ + 1)) - (varphi R S ↑⌊a2⌋)) * fract a2 = ((varphi R S (↑⌊a2⌋ + 1)) - (varphi R S ↑⌊a2⌋)) * (a1 - a2) := by
    unfold fract
    calc
      ((varphi R S (↑⌊a2⌋ + 1)) - (varphi R S ↑⌊a2⌋)) * (a1 - ↑⌊a2⌋) - ((varphi R S (↑⌊a2⌋ + 1)) - (varphi R S ↑⌊a2⌋)) * (a2 - ⌊a2⌋) = ((varphi R S (↑⌊a2⌋ + 1)) - (varphi R S ↑⌊a2⌋)) * ((a1 - ⌊a2⌋) - (a2 - ⌊a2⌋)) := by
        ring
      _ = ((varphi R S (↑⌊a2⌋ + 1)) - (varphi R S ↑⌊a2⌋)) * (a1 - a2) := by
        simp
        left
        unfold fract
        ring
  rw [this]
  apply mul_neg_iff.2
  left
  constructor
  simp
  convert varphi_mono_int R S ⌊a2⌋ (⌊a2⌋ + 1) (by simp)
  simp
  simp [h2]

--i'll change this name too
theorem varphi_mono_over_section : ∀ a1 a2 : ℚ , (⌊a1⌋ ≠ ⌊a2⌋) ∧ (a1 < a2) → (varphi R S a1) < (varphi R S a2) := by
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
  have h1 : (varphi R S a1) < (varphi R S (⌊a1⌋ + 1)) := by apply (varphi_lt_ceil R S)
  apply h1
  have h2 : (varphi R S (⌊a1⌋ + 1)) ≤ (varphi R S a2) := by
    by_cases heq : (⌊a1⌋ + 1) = a2
    simp [heq]
    push_neg at heq
    have h1' : (varphi R S (⌊a1⌋ + 1)) ≤ (varphi R S ⌊a2⌋) := by
      convert varphi_mono_int' R S (⌊a1⌋ + 1) ⌊a2⌋ hle
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
  have h1 : (varphi R S a1) ≤ (varphi R S ⌊a2⌋) := by
    by_cases heq : a1 = ⌊a2⌋
    simp [heq]
    apply le_of_lt
    apply lt_of_lt_of_le
    push_neg at *
    have hlt' : a1 < ⌊a2⌋ := by apply lt_of_le_of_ne hle heq
    have h1' : (varphi R S a1) < (varphi R S (⌊a1⌋ + 1)) := by apply varphi_lt_ceil R S
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
    have h2' : (varphi R S ↑(⌊a1⌋ + 1)) ≤ (varphi R S (⌊a2⌋)) := by
      apply varphi_mono_int' R S (⌊a1⌋ + 1) ⌊a2⌋ hle'
    convert h2'
    simp
  apply h1
  push_neg at hfloor
  have h2 : (varphi R S ⌊a2⌋) < (varphi R S a2) := by apply (varphi_gt_floor R S a2 hfloor)
  apply h2

theorem varphi_mono_iff : (∀a1 a2 : ℚ , a1 < a2 → (varphi R S a1) < (varphi R S a2)) ↔ (∀a1 a2 : ℤ , a1 < a2 → (varphi R S a1) < (varphi R S a2)) := by
  constructor
  rintro h a1 a2
  apply varphi_mono_int R S a1 a2
  rintro h a1 a2 h'
  by_cases hfloor : ⌊a1⌋ = ⌊a2⌋
  apply varphi_mono_in_section
  constructor <;> assumption
  push_neg at *
  apply varphi_mono_over_section
  constructor <;> assumption

theorem varphi_mono : ∀a1 a2 : ℚ , a1 < a2 → (varphi R S a1) < (varphi R S a2) := by
  apply (varphi_mono_iff R S).2
  apply varphi_mono_int

theorem varphi_bij : Function.Bijective (varphi R S) := by
  constructor
  rintro a1 a2 h
  contrapose! h
  by_cases h1 : a1 > a2
  have hlt : (varphi R S a2) < (varphi R S a1) := by
    apply varphi_mono
    apply h1
  apply ne_of_gt hlt
  have hlt : (varphi R S a2) > (varphi R S a1) := by
    apply varphi_mono
    apply lt_of_not_ge
    push_neg at *
    exact lt_of_le_of_ne h1 h
  apply ne_of_lt hlt
  rintro b
  unfold varphi varphi'
  by_cases hb : b < 0
  sorry
  sorry

noncomputable def psi : ℚ → ℚ :=
  invFun (varphi R S)

theorem psi_bij : Function.Bijective (psi R S) := by
  constructor
  have hpsi: (invFun (varphi R S)).Injective :=
    (rightInverse_invFun (varphi_bij R S).2).injective
  exact hpsi
  apply invFun_surjective
  apply (varphi_bij R S).1

theorem varphi_zero_eq_zero : varphi R S 0 = 0 := by
  unfold varphi
  simp

noncomputable def psi' (v : ℚ): ℚ :=
  1 / (varphi' R S (psi R S v))

theorem psi_zero_eq_zero : psi R S 0 = 0 := by
  unfold psi
  nth_rw 1 [← varphi_zero_eq_zero R S]
  have : id 0 = (0 : ℚ) := by rfl
  nth_rw 2 [← this]
  have Inj : (varphi R S).Injective := by apply (varphi_bij R S).1
  rw [← invFun_comp Inj]
  simp

theorem varphi_inv_psi : ∀ a : ℚ , varphi R S (psi R S a) = a := by
  rintro a
  apply invFun_eq
  apply (varphi_bij R S).surjective

--lemma 3
variable [Field R] [Field S] [Module R S] [FiniteDimensional R S]

open scoped Classical

theorem Varphi_eq_Sum_Inf_Int (u : ℤ) [Fintype (S ≃ₐv[R] S)] : (varphi R S u) = (1 / Nat.card G(S/R)_[0]) * (∑ x : (S ≃ₐv[R] S) , ((ValAlgEquiv.truncatedLowerIndex R S x (u + 1))))- 1 := by sorry



theorem Varphi_eq_Sum_Inf (u : ℚ) [Fintype (S ≃ₐv[R] S)] : (varphi R S u) = (1 / Nat.card G(S/R)_[0]) * (∑ x : (S ≃ₐv[R] S) , ((ValAlgEquiv.truncatedLowerIndex R S x (u + 1))))- 1 := by
  unfold varphi varphi' ValAlgEquiv.truncatedLowerIndex
  by_cases h : u ≥ 1
  simp [h]
  sorry
  sorry
