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

/--definition of varphi and psi-/
noncomputable def varphi' (u : ℝ) : ℝ :=
  1/(relindex' G(vL/vK)_[0] G(vL/vK)_[(Int.ceil u)])

noncomputable def varphi (u : ℝ) : ℝ :=
  ∫ x in Ioc 0 u, (varphi' vK vL x)

noncomputable def psi : ℝ → ℝ :=
  invFun (varphi vK vL)

theorem varphi_zero_eq_zero : varphi vK vL 0 = 0 := by
  unfold varphi
  simp

theorem varphi_negone_eq_negone : varphi vK vL -1 = -1 := by
  sorry


noncomputable def psi' (v : ℝ): ℝ :=
  1 / (varphi' vK vL (psi vK vL v))

--some elementary properties of varphi and psi
noncomputable def index_of_G_i (i : ℤ) := relindex' G(vL/vK)_[1] G(vL/vK)_[(Int.ceil i + 1)]

theorem Varphi_eq_Sum {m : ℤ} {u : ℝ} (h1 : m > 1) (h2 : m ≤ u ∧ u ≤ m + 1) : ((varphi vK vL u) = ∑ x in Finset.Icc 0 m, (index_of_G_i vK vL x) + (u - (m : ℝ)) / index_of_G_i vK vL (Int.ceil u)) := by
  unfold varphi varphi'
  simp
  have : ∫ x in (Ioc (Int.ceil (u - 1) : ℝ) u), (varphi' vK vL x) = (u - (Int.ceil (u - 1))) * (index_of_G_i vK vL (Int.ceil u)) := by
    sorry
  have : ∀ i : ℤ , index_of_G_i vK vL i = (i - Int.ceil (i - 1)) * (index_of_G_i vK vL i) := by
    simp
  have : ∑ x in Finset.Icc 0 m, (index_of_G_i vK vL x) + (u - (m : ℝ)) / index_of_G_i vK vL (Int.ceil u) = ∑ t in Finset.Icc 0 m, ∫ x in (Ioc (Int.ceil (t - 1) : ℝ) t), (varphi' vK vL x) + ∫ x in (Ioc (Int.ceil (u - 1) : ℝ) u), (varphi' vK vL x) := by
    sorry
  sorry


theorem psi_zero_eq_zero : psi vK vL 0 = 0 := by
  unfold psi
  simp only [invFun]



theorem varphi_bij : Function.Bijective (varphi vK vL) := by
  constructor
  unfold varphi
  intro a1 a2 ha
  sorry
  unfold varphi
  intro b
  sorry


theorem psi_bij : Function.Bijective (psi vK vL) := by
  constructor
  sorry
  apply invFun_surjective
  sorry

--lemma 3
theorem Varphi_eq_Sum_Inf (u : ℝ) : (varphi vK vL u) = (1 / Nat.card G(vL/vK)_[0]) * (∑ x in G(vL/vK)_[(Int.ceil u)] , min (u + 1) ((i[vL/vK] x)))- 1 := by sorry

--lemma 4
