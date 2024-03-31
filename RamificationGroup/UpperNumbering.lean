import RamificationGroup.LowerNumbering
import Mathlib.RingTheory.Valuation.Basic
import RamificationGroup.HerbrandFunction
import RamificationGroup.Valued.Hom.Discrete'

open QuotientGroup IntermediateField DiscreteValuation Valued Valuation
open HerbrandFunction

section

-- principle : first try to state a theorem in IsScalarTower, then try IntermediateField
variable {K L : Type*} {ΓK : outParam Type*} [Field K] [Field L] [LinearOrderedCommGroupWithZero ΓK] [vK : Valued K ΓK] [vL : Valued L ℤₘ₀] [ValAlgebra K L] {H : Subgroup (L ≃ₐ[K] L)} [Subgroup.Normal H] {K' : IntermediateField K L}

/-
--lemma 4
theorem Varphi_With_i (σ : (L ≃ₐ[K] L) ⧸ H) : (varphi K L (Sup (i_[L/K] ((mk' H)⁻¹' {σ})))) = (i_[L/K'] σ) - (1 : WithTop ℤ):= by sorry

-/

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [ValAlgebra R S] (x : ℚ)
#check Int.ceil
#check φ_[L/K] x
#check ψ_[L/K] x

namespace HerbrandFunction

-- Prop 15
-- probably need to rename
theorem phi_comp_of_intermediateField : (phi K' L) ∘ (phi K K') = phi K L := by
  ext u
  sorry

--Prop 15
theorem psi_comp_of_intermediateField : (psi K K') ∘ (psi K' L) = psi K L := by
  ext v
  sorry

end HerbrandFunction

-- aux construction of upper numbering ramification group, correct for finite extension of local fields only. later we define a more general version on all algebraic extensions of local fields.
def upperRamificationGroup_aux (v : ℚ): (Subgroup (S ≃ₐv[R] S)) := lowerRamificationGroup R S ⌈ψ_[S/R] v⌉

scoped [Valued] notation:max " G(" L:max "/" K:max ")^[" u:max "] " => upperRamificationGroup_aux K L u

end

section

open DiscreteValuation

variable {K L : Type*} {ΓK : outParam Type*} [Field K] [Field L] [vK : Valued K ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK.v] [IsDiscrete vL.v] [ValAlgebra K L] {H : Subgroup (L ≃ₐ[K] L)} [Subgroup.Normal H] {K' : IntermediateField K L}

#synth Valued K' ℤₘ₀

#check valuedIntermediateField -- this should be renamed

variable (v : ℚ)
#check (G(L/K)^[v]).subgroupOf (H.comap ValAlgEquiv.toAlgEquivₘ)

#check AlgEquiv.restrictNormalHom

namespace ValAlgEquiv

variable (K') {ΓK' : outParam Type*} [Field K'] [LinearOrderedCommGroupWithZero ΓK'] [Valued K' ΓK'] [ValAlgebra K K'] [ValAlgebra K' L] [IsScalarTower K K' L]
-- change this using IsScalatower

def restrictNormalHom : (L ≃ₐv[K] L) →* K' ≃ₐv[K] K' := sorry

end ValAlgEquiv

variable [FiniteDimensional K L]

#synth Fintype (L ≃ₐ[K] L)
instance : Fintype (L ≃ₐv[K] L) := sorry

-- Lemma 4
def HerbrandFunction.j (σ : L ≃ₐv[K'] L) : sorry := sorry

variable {σ : K' ≃ₐv[K] K'}
open Classical
#synth Fintype ((ValAlgEquiv.restrictNormalHom K')⁻¹' {σ})

-- split j out
theorem Varphi_With_i (u : ℚ) (σ : K' ≃ₐv[K] K') : (phi K L (Finset.sup'  ((ValAlgEquiv.restrictNormalHom K')⁻¹' {σ}).toFinset sorry (fun x => x.truncatedLowerIndex K L u) )) = σ.truncatedLowerIndex K K' (sorry) - 1:= by sorry


-- Lemma 5
@[simp]
theorem herbrand (u : ℚ) : G(L/K)_[⌈u⌉].map (ValAlgEquiv.restrictNormalHom K') = G(K'/K)_[⌈phi K L u⌉] := by sorry

@[simp]
theorem herbrand' [Normal K K'] (v : ℚ) : G(L/K)^[v].map (ValAlgEquiv.restrictNormalHom K') = G(K'/K)^[v] := by
  convert herbrand (ψ_[L/K] v)
  sorry

end
