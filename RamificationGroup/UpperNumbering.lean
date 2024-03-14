--import RamificationGroup.LowerNumbering
import RamificationGroup.Unused.Definition.Herbrand

def ValAlgEquiv.upperIndex {K L} [Field K] [Field L] [DiscretelyValued K] [DiscretelyValued L] [ValAlgebra K L]
(s : L ≃ₐv[K] L) : WithTop ℕ := sorry

def upperRamificationGroup {K L} [Field K] [Field L] [DiscretelyValued K] [DiscretelyValued L] [ValAlgebra K L]
(i : ℝ) : Subgroup (L ≃ₐv[K] L) := sorry

notation : max "G(" L:max "/" K:max ")^[" n:max "]" => upperRamificationGroup K L n

variable {K K' L : Type*} [Field K] [Field K'] [Field L] (vK : Valuation K ℤₘ₀) (vK' : Valuation K' ℤₘ₀) (vL : Valuation L ℤₘ₀)
[Algebra K K'] [Algebra K L] [Algebra K' L] [IsScalarTower K K' L] [ValuationExtension vK vL] [ValuationExtension vK' vL]
--lemma 4
theorem Varphi_With_i (σ : L ≃ₐ[K'] L) :(varphi vL vK' ()) = (i[vL/vK'] σ) - 1:= by sorry

--lemma 5
theorem Herbrand_Thm : := by sorry

--prop 15


theorem varphi_comp_field_ext :Function.comp (varphi vK' vK) (varphi vL vK') = varphi vL vK:= by sorry

theorem psi_comp_field_ext :Function.comp (psi vL vK') (psi vK' vK) = psi vL vK:= by sorry
