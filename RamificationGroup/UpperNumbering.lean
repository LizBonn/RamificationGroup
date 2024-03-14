--import RamificationGroup.Unused.Definition.LowerNumbering
import RamificationGroup.LowerNumbering
import Mathlib.FieldTheory.Galois
import Mathlib.RingTheory.Valuation.Basic
import RamificationGroup.Unused.Definition.Herbrand

open QuotientGroup IntermediateField

def ValAlgEquiv.upperIndex {K L} [Field K] [Field L] [DiscretelyValued K] [DiscretelyValued L] [ValAlgebra K L]
(s : L ≃ₐv[K] L) : WithTop ℕ := sorry

def upperRamificationGroup {K L} [Field K] [Field L] [DiscretelyValued K] [DiscretelyValued L] [ValAlgebra K L]
(i : ℝ) : Subgroup (L ≃ₐv[K] L) := sorry

notation : max "G(" L:max "/" K:max ")^[" n:max "]" => upperRamificationGroup K L n

variable {K L : Type*} [Field K][Field L] (vK : Valuation K ℤₘ₀) (vL : Valuation L ℤₘ₀)
[Algebra K L] [ValuationExtension vK vL] {H : Subgroup (L ≃ₐ[K] L)} [Subgroup.Normal H] (vK' : Valuation (fixedField H) ℤₘ₀) [ValuationExtension vK' vL]
--{K'' : IntermediateField K L}

--lemma 4
theorem Varphi_With_i (σ : (L ≃ₐ[K] L) ⧸ H) :(varphi vL vK' (Sup (i[vL/vK'] ((mk' H)⁻¹' {σ})))) = (i[vL/vK'] σ) - 1:= by sorry

--lemma 5
theorem Herbrand_Thm {u : ℝ} {v : ℝ} (h : v = varphi vL vK u) {H : Subgroup (L ≃ₐ[K] L)} [Subgroup.Normal H]: G(vL/vK')_[v] = (G(vL/vK)_[u] ⊔ H) ⧸ H:= by sorry

--prop 15
theorem varphi_comp_field_ext : (varphi vK' vK) ∘ (varphi vL vK') = varphi vL vK:= by sorry

theorem psi_comp_field_ext : (psi vL vK') ∘ (psi vK' vK) = psi vL vK:= by sorry
