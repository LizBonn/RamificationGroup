import RamificationGroup.LowerNumbering
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import RamificationGroup.Unused.MissingPiecesOfMathlib
import Mathlib.GroupTheory.Index
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Algebra.BigOperators.Basic

--definition of varphi and psi

open DiscreteValuation Subgroup Set Function MeasureTheory Finset BigOperators

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

theorem varphi_mono_int : ∀a1 a2 : ℤ , a1 < a2 → (varphi R S a1) < (varphi R S a2) := by
  rintro a1 a2 h
  induction' a2 with n ih
  sorry
  sorry

--I will change this name
theorem varphi_lt_int_ceil : ∀a : ℚ , a ≠ (Int.ceil a) → (varphi R S a) < (varphi R S (Int.ceil a))  := by sorry

theorem varphi_mono_section : ∀a1 a2 : ℚ , (Int.floor a1) = (Int.floor a2) ∧ (a1 > a2) → (varphi R S a1) > (varphi R S a2) := by
  rintro a1 a2 ⟨h1, h2⟩
  apply gt_iff_lt.2
  apply sub_lt_zero.1
  have hsub: (varphi R S a2) - (varphi R S a1) = (a2 - a1) * (varphi' R S a1) := by
    have h' : varphi' R S a1 = varphi' R S a2 := by
      unfold varphi' Index_of_G_i
      have hceil : Int.ceil a1 = Int.ceil a2 := by
        sorry
      sorry
    unfold varphi
    by_cases ha2 : 1 ≤ a2
    have : 1 ≤ a1 := by linarith [h2]
    simp [ha2, this, h1, h']
    sorry
    sorry
  have hge: (varphi R S a2) - (varphi R S a1) < 0 := by
    simp [hsub]
    apply mul_neg_iff.2
    right
    constructor
    linarith [h2]
    apply varphi'_pos R S
  exact hge

theorem varphi_mono : ∀a1 a2 : ℚ , a1 > a2 → (varphi R S a1) > (varphi R S a2) := by
  rintro a1 a2 h
  by_cases h1 : (Int.floor a1) = (Int.floor a2)
  exact varphi_mono_section R S a1 a2 ⟨h1, h⟩
  have ha1 : varphi R S a1 ≥ varphi R S (Int.floor a1) := by
    by_cases hequl : a1 = Int.floor a1
    nth_rw 1 [hequl]
    have hgt : varphi R S a1 > varphi R S (Int.floor a1) := by
      have hgt' : a1 > Int.floor a1 := by
        sorry
      apply varphi_mono_section R S a1 (Int.floor a1) ⟨rfl,hgt'⟩
    sorry
  have h'' : Int.floor a1 > a2 := by
    by_contra hngt
    push_neg at hngt
    have hflooreq : Int.floor a1 = Int.floor a2 := by
      have hfloorle : Int.floor a1 ≤ Int.floor a2 := by
        apply Int.le_floor.2 hngt
      have hfloorge : Int.floor a2 ≤ Int.floor a1 := by
        apply Int.floor_le_floor
        apply le_of_lt
        simp [h]
      apply (LE.le.ge_iff_eq hfloorle).1 hfloorge
    contradiction
  have ha2 : varphi R S (Int.floor a1) > varphi R S a2 := by
    have hcllefl : Int.ceil a2 ≤ Int.floor a1 := by
      apply Int.ceil_le.2
      apply le_of_lt h''
    by_cases heqceil : a2 = Int.ceil a2
    have hclltfl : Int.ceil a2 < Int.floor a1 := by
      by_contra hn
      push_neg at hn
      have hcleqfl : Int.ceil a2 = Int.floor a1 := by
        apply (LE.le.ge_iff_eq hcllefl).1 hn
      have hfleqfl : Int.floor a1 = Int.floor a2 := by
        sorry
      contradiction
    sorry
    have hphiclltfl : varphi R S (Int.ceil a2) < varphi R S (Int.floor a1) := by
      apply varphi_mono_int
      sorry
--      assumption
--    rw [heqceil]
    simp [hphiclltfl]
    have hflcl : varphi R S (Int.ceil a2) ≤ varphi R S (Int.floor a1) := by
      by_cases hfleqcl : Int.ceil a2 = Int.floor a1
      simp [hfleqcl]
      have hflgtcl : Int.ceil a2 < Int.floor a1 := by
        push_neg at hfleqcl
        apply lt_of_le_of_ne hcllefl hfleqcl
      apply le_of_lt
      apply varphi_mono_int
      exact hflgtcl
    have hcl : varphi R S a2 < varphi R S (Int.ceil a2) := by
      push_neg at heqceil
      apply varphi_lt_int_ceil
      assumption
  apply gt_of_ge_of_gt
  apply ha1
  apply ha2

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

--do I really need this?
theorem varphi_negone_eq_negone : varphi R S (-1) = -1 := by
  unfold varphi varphi'
  simp
  sorry

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
  unfold varphi
  apply mul_eq_mul_right_iff.1 (Nat.card G(S/R)_[0])
#check WithTop ℤ
