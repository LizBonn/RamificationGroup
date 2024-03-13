--import RamificationGroup.Unused.Definition.LowerNumbering
import Mathlib.MeasureTheory.Integral.IntervalIntegral
--import RamificationGroup.Unused.Definition.MissingPiecesOfMathlib

open DiscreteValuation

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (vK : Valuation K ℤₘ₀) (vL : Valuation L ℤₘ₀) [ValuationExtension vK vL]

def varphi' (u : ℚ) : ℚ :=
  1/(relindex' G(vL/vK)_[1] G(vL/vK)_[u + 1])

def varphi (u : ℚ) : ℚ :=
  ∫ x in 0..u, varphi' u
