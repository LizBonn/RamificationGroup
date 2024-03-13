import RamificationGroup.Unused.Definition.LowerNumbering
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import RamificationGroup.Unused.MissingPiecesOfMathlib
import Mathlib.GroupTheory.Index
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Algebra.BigOperators.Basic


--definition of varphi and psi

open DiscreteValuation Subgroup Set Function MeasureTheory Finset

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (vK : Valuation K ℤₘ₀) (vL : Valuation L ℤₘ₀) [ValuationExtension vK vL]
variable {μ : Measure ℝ}
variable (vK : Valuation K ℤₘ₀) (vL : Valuation L ℤₘ₀) [ValuationExtension vK vL]

noncomputable def varphi' (u : ℝ) : ℝ :=
  1/(relindex' G(vL/vK)_[1] G(vL/vK)_[(Int.ceil u + 1)])

noncomputable def varphi (u : ℝ) : ℝ :=
  ∫ x in Ioc 0 u, (varphi' vK vL u)

noncomputable def psi : ℝ → ℝ :=
  invFun (varphi vK vL)

theorem varphi_zero_eq_zero : varphi vK vL 0 = 0 := sorry

theorem varphi_none_eq_none : varphi vK vL -1 = -1 := sorry

noncomputable def psi' (v : ℝ): ℝ :=
  1 / (varphi' vK vL (psi vK vL v))

--some elementary properties of varphi and psi
noncomputable def index_of_G_i (i : ℤ) := relindex' G(vL/vK)_[1] G(vL/vK)_[(Int.ceil i + 1)]

theorem Varphi_eq_Sum {m : ℕ} {u : ℝ} (h1 : m > 1) (h2 : m ≤ u ∧ u ≤ m + 1) : ((varphi vK vL u) = (Finset.sum (Finset m) (index_of_G_i vK vL)) + (u - (m : ℝ)) / index_of_G_i vK vL (Int.ceil u)) := by sorry

theorem psi_zero_eq_zero : psi vK vL 0 = 0 := by sorry

theorem varphi_bij : Function.Bijective (varphi vK vL) := by sorry

theorem psi_bij : Function.Bijective (psi vK vL) := by sorry
