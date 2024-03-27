import RamificationGroup.LowerNumbering
import Mathlib.RingTheory.Valuation.Basic
import RamificationGroup.Valuation.Trash.test

open QuotientGroup IntermediateField DiscreteValuation Valued Valuation

variable (K L : Type*) {ΓK : outParam Type*} [Field K] [Field L] [LinearOrderedCommGroupWithZero ΓK] [vK : Valued K ΓK] [vS : Valued L ℤₘ₀] [ValAlgebra K L] {H : Subgroup (L ≃ₐ[K] L)} [Subgroup.Normal H]
{K' : fixedField H}

--lemma 4
theorem Varphi_With_i (σ : (L ≃ₐ[K] L) ⧸ H) : (varphi K L (Sup (i_[L/K] ((mk' H)⁻¹' {σ})))) = (i_[L/K'] σ) - (1 : WithTop ℤ):= by sorry

--lemma 5
theorem Herbrand_Thm {u : ℚ} {v : ℚ} (h : v = varphi K L u) {H : Subgroup (L ≃ₐv[K] L)} [Subgroup.Normal H]: G(L/K')_[(Int.ceil v)] = (G(L/K)_[(Int.ceil u)] ⊔ H) ⧸ H:= by sorry

--prop 15
theorem varphi_comp_field_ext : (varphi K K') ∘ (varphi K' L) = varphi K L:= by sorry

theorem psi_comp_field_ext : (psi K K') ∘ (psi K' L) = psi K L:= by sorry
