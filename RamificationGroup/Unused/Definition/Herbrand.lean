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
variable {μ : Measure ℝ}
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
  else if u < 1 ∧ 0 ≤ u then
    u * (varphi' vK vL u)
  else
    (-u) * (varphi' vK vL u)

noncomputable def psi : ℚ → ℚ :=
  invFun (varphi vK vL)

theorem varphi_zero_eq_zero : varphi vK vL 0 = 0 := by
  unfold varphi
  simp

theorem varphi_negone_eq_negone : varphi vK vL -1 = -1 := by
  unfold varphi varphi'
  sorry

noncomputable def psi' (v : ℚ): ℚ :=
  1 / (varphi' vK vL (psi vK vL v))

theorem psi_zero_eq_zero : psi vK vL 0 = 0 := by
  unfold psi
  simp only [invFun]


theorem varphi_bij : Function.Bijective (varphi vK vL) := by sorry

theorem psi_bij : Function.Bijective (psi vK vL) := by sorry

--lemma 3
theorem Varphi_eq_Sum_Inf (u : ℚ) : (varphi vK vL u) = (1 / Nat.card G(vL/vK)_[0]) * (∑ x in (Finset G(vL/vK)_[(Int.ceil u)]) , min (u + 1) ((i[vL/vK] x)))- 1 := by sorry
