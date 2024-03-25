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

theorem varphi_mono_int : ∀a1 a2 : ℤ , a1 < a2 → (varphi R S a1) < (varphi R S a2) := by
  rintro a1 a2 h
  induction' a2 with n ih
  sorry
  sorry

--i'll change this name
theorem varphi_rational_floor : ∀ a : ℚ , (varphi R S a) = (varphi R S ⌊a⌋) + ((varphi R S (⌊a⌋ + 1)) - (varphi R S ⌊a⌋)) * (a - ⌊a⌋) := by
  rintro a
  unfold varphi
  by_cases ha : a ≥ 1
  have hfl : 1 ≤ ↑⌊a⌋ := by sorry
  simp [ha, hfl]
  sorry
  sorry

theorem varphi_rational_ceil : ∀ a : ℚ , (varphi R S a) = (varphi R S (⌊a⌋ + 1)) - ((varphi R S (⌊a⌋ + 1)) - (varphi R S ⌊a⌋)) * (⌊a⌋ - a + 1) := by sorry

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
  sorry
  apply fract_pos.2 ha

theorem varphi_mono_section : ∀ a1 a2 : ℚ , (⌊a1⌋ = ⌊a2⌋) ∧ (a1 < a2) → (varphi R S a1) < (varphi R S a2) := by
  rintro a1 a2 ⟨h1, h2⟩
  apply gt_iff_lt.2
  apply sub_lt_zero.1
  rw [varphi_rational_floor]
  sorry

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
  sorry
  have : ⌊a⌋ - a > (-1) := by sorry
  linarith [this]

theorem varphi_mono_iff : (∀a1 a2 : ℚ , a1 < a2 → (varphi R S a1) < (varphi R S a2)) ↔ (∀a1 a2 : ℤ , a1 < a2 → (varphi R S a1) < (varphi R S a2)) := by
  constructor
  rintro h
  sorry
  rintro h a1 a2 h'
  by_cases hfloor : ⌊a1⌋ = ⌊a2⌋
  apply varphi_mono_section
  constructor <;> assumption
  sorry

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

--lemma 3
variable [Field R] [Field S] [Module R S] [FiniteDimensional R S]

open scoped Classical

theorem Varphi_eq_Sum_Inf (u : ℚ) [Fintype (S ≃ₐv[R] S)] : (varphi R S u) = (1 / Nat.card G(S/R)_[0]) * (∑ x : (S ≃ₐv[R] S) , ((ValAlgEquiv.truncatedLowerIndex R S x (u + 1))))- 1 := by
  unfold varphi varphi' ValAlgEquiv.truncatedLowerIndex
  by_cases h : u ≥ 1
  simp [h]
  sorry
  sorry
