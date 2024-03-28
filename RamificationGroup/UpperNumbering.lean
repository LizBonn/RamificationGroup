import RamificationGroup.LowerNumbering
import Mathlib.RingTheory.Valuation.Basic
import RamificationGroup.HerbrandFunction
-- import RamificationGroup.Valuation.Trash.test

open QuotientGroup IntermediateField DiscreteValuation Valued Valuation
open HerbrandFunction

variable {K L : Type*} {ΓK : outParam Type*} [Field K] [Field L] [LinearOrderedCommGroupWithZero ΓK] [vK : Valued K ΓK] [vL : Valued L ℤₘ₀] [ValAlgebra K L] {H : Subgroup (L ≃ₐ[K] L)} [Subgroup.Normal H] {K' : IntermediateField K L}

/-
--lemma 4
theorem Varphi_With_i (σ : (L ≃ₐ[K] L) ⧸ H) : (varphi K L (Sup (i_[L/K] ((mk' H)⁻¹' {σ})))) = (i_[L/K'] σ) - (1 : WithTop ℤ):= by sorry

--lemma 5
theorem Herbrand_Thm {u : ℚ} {v : ℚ} (h : v = varphi K L u) {H : Subgroup (L ≃ₐv[K] L)} [Subgroup.Normal H]: G(L/K')_[(Int.ceil v)] = (G(L/K)_[(Int.ceil u)] ⊔ H) ⧸ H:= by sorry

--prop 15
theorem varphi_comp_field_ext : (varphi K K') ∘ (varphi K' L) = varphi K L:= by sorry

theorem psi_comp_field_ext : (psi K K') ∘ (psi K' L) = psi K L:= by sorry

-/

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [ValAlgebra R S] (x : ℚ)
#check Int.ceil
#check φ_[L/K](x)
#check ψ_[L/K](x)
-- aux construction of upper numbering ramification group, correct for finite extension of local fields only. later we define a more general version on all algebraic extensions of local fields.
def upperRamificationGroup_aux (u : ℚ): (Subgroup (S ≃ₐv[R] S)) := lowerRamificationGroup R S ⌈ψ_[S/R](u)⌉

scoped [Valued] notation:max " G(" L:max "/" K:max ")^[" u:max "] " => upperRamificationGroup_aux K L u

namespace DiscreteValuation
-- should be in file talking about both Discrete and ValAlgHom, probably Hom.Discrete
scoped instance valuedIntermediateField: Valued K' ℤₘ₀ := sorry

scoped instance : IsDiscrete ((valuedIntermediateField (K':= K')).v) := sorry

scoped instance : ValAlgebra K' L := sorry

scoped instance : ValAlgebra K K' := sorry

end DiscreteValuation

open DiscreteValuation

#synth Valued K' ℤₘ₀

#check valuedIntermediateField

variable (u : ℚ)
#check (G(L/K)^[u]).subgroupOf (H.comap ValAlgEquiv.toAlgEquivₘ)

variable (K') in
def ValAlgEquiv.restrictNormalHom : (L ≃ₐv[K] L) →* K' ≃ₐv[K] K' := sorry

theorem herbrand' [Normal K K'] (u : ℚ) : G(K'/K)^[u] = G(L/K)^[u].map (ValAlgEquiv.restrictNormalHom K'):= by sorry
