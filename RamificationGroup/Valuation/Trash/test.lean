import RamificationGroup.Unused.Definition.LowerNumbering
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import RamificationGroup.Unused.MissingPiecesOfMathlib
import Mathlib.GroupTheory.Index
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Algebra.BigOperators.Basic

--definition of varphi and psi

open DiscreteValuation Subgroup Set Function MeasureTheory Finset BigOperators

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (vK : Valuation K ℤₘ₀) (vL : Valuation L ℤₘ₀) [ValuationExtension vK vL]
variable (vK : Valuation K ℤₘ₀) (vL : Valuation L ℤₘ₀) [ValuationExtension vK vL]

noncomputable def Index_of_G_i (u : ℚ) : ℚ :=
  if u > 0 then
    relindex' G(vL/vK)_[0] G(vL/vK)_[(Int.ceil u)]
  else
    relindex' G(vL/vK)_[0] G(vL/vK)_[(Int.floor u)]

noncomputable def varphi' (u : ℚ) : ℚ :=
  1 / (Index_of_G_i vK vL u)

noncomputable def varphi (u : ℚ) : ℚ :=
  if u ≥ 1 then
    ∑ x in Finset.Icc 0 (Int.floor u), (varphi' vK vL x) + (u - (Int.floor u)) * (varphi' vK vL u)
  else
    u * (varphi' vK vL u)

theorem varphi_mono : ∀ a1 a2 : ℚ , a1 > a2 → (varphi vK vL a1) > (varphi vK vL a2) := by
  rintro a1 a2 h
  unfold varphi
  sorry

theorem varphi_bij : Function.Bijective (varphi vK vL) := by
  constructor
  rintro a1 a2 h
  contrapose! h
  by_cases h1 : a1 > a2
  have hlt : (varphi vK vL a2) < (varphi vK vL a1) := by
    apply varphi_mono
    apply h1
  apply ne_of_gt hlt
  have hlt : (varphi vK vL a2) > (varphi vK vL a1) := by
    apply varphi_mono
    apply lt_of_not_ge
    push_neg at *
    exact lt_of_le_of_ne h1 h
  apply ne_of_lt hlt
  rintro b
  sorry

noncomputable def psi : ℚ → ℚ :=
  invFun (varphi vK vL)

theorem psi_bij : Function.Bijective (psi vK vL) := by
  constructor
  have hpsi: (invFun (varphi vK vL)).Injective :=
    (rightInverse_invFun (varphi_bij vK vL).2).injective
  exact hpsi
  apply invFun_surjective
  apply (varphi_bij vK vL).1

theorem varphi_zero_eq_zero : varphi vK vL 0 = 0 := by
  unfold varphi
  simp

--do I really need this?
theorem varphi_negone_eq_negone : varphi vK vL (-1) = -1 := by
  unfold varphi varphi'
  simp
  sorry

noncomputable def psi' (v : ℚ): ℚ :=
  1 / (varphi' vK vL (psi vK vL v))

theorem psi_zero_eq_zero : psi vK vL 0 = 0 := by
  unfold psi
  nth_rw 1 [← varphi_zero_eq_zero vK vL]
  have : id 0 = (0 : ℚ) := by rfl
  nth_rw 2 [← this]
  have Inj : (varphi vK vL).Injective := by apply (varphi_bij vK vL).1
  rw [← invFun_comp Inj]
  simp

--lemma 3
variable [FiniteDimensional K L]

open scoped Classical

theorem Varphi_eq_Sum_Inf (u : ℚ) : (varphi vK vL u) = (1 / Nat.card G(vL/vK)_[0]) * (∑ x : G(vL/vK)_[(Int.ceil u)] , min (u + 1) ((i[vL/vK] x)))- 1 := by sorry
