import RamificationGroup.LowerNumbering
import Mathlib.RingTheory.Valuation.Basic
import RamificationGroup.HerbrandFunction
import RamificationGroup.Valued.Hom.Discrete'

open QuotientGroup IntermediateField DiscreteValuation Valued Valuation Subgroup Set

variable (K L : Type*) {ΓK : outParam Type*} [Field K] [Field L] [LinearOrderedCommGroupWithZero ΓK] [vK : Valued K ΓK] [vS : Valued L ℤₘ₀] [ValAlgebra K L] {H : Subgroup (L ≃ₐ[K] L)} [Subgroup.Normal H]

def Lift_Galois_ValEquiv : (L ≃ₐ[K] L) →* (L ≃ₐv[K] L) := by sorry

def Galois_to_Quotient : (L ≃ₐ[(fixedField H)] L) →* (L ≃ₐ[K] L) ⧸ H := by sorry

instance : Valued (fixedField H) ℤₘ₀ where
  uniformContinuous_sub := sorry
  v := sorry
  is_topological_valuation := sorry

attribute [-instance] Subtype.preorder
instance : ValAlgebra K (fixedField H) :=
{
  algebra (fixedField H) with
  monotone' := sorry
  continuous_toFun := sorry
  val_isEquiv_comap := sorry
}

instance : ValAlgebra (fixedField H) L :=
{
  Subalgebra.toAlgebra (fixedField H).toSubalgebra with
  monotone' := sorry
  continuous_toFun := sorry
  val_isEquiv_comap := sorry
}

variable {K L : Type*} {ΓK : outParam Type*} [Field K] [Field L] [LinearOrderedCommGroupWithZero ΓK] [vK : Valued K ΓK] [vL : Valued L ℤₘ₀] [ValAlgebra K L] {H : Subgroup (L ≃ₐ[K] L)} [Subgroup.Normal H] {K' : IntermediateField K L}

/-
--lemma 4
theorem Varphi_With_i' (σ : (L ≃ₐ[(fixedField H)] L)) : (varphi K L (sSup (i_[L/K] '' ((Lift_Galois_ValEquiv K L) '' ((mk' H)⁻¹' {(Galois_to_Quotient K L σ)}))))) = (i_[L/(fixedField H)] ((Lift_Galois_ValEquiv (fixedField H) L) σ)) - (1 : ℕ∞) := by sorry

--lemma 5
theorem Herbrand_Thm {u : ℚ} {v : ℚ} (h : v = varphi K L u) : G(L/(fixedField H))_[(Int.ceil v)] = (_ ⧸ H.subgroupOf ((G(L/K)_[(Int.ceil u)].comap (Lift_Galois_ValEquiv K L)) ⊔ H)) := by sorry

open Set
variable {u : ℚ} {σ : (L ≃ₐ[(fixedField H)] L)} {t : ((mk' H)⁻¹' {(Galois_to_Quotient K L σ)})}
#check (G(L/K)_[(Int.ceil u)].comap (Lift_Galois_ValEquiv K L))
#check H
#check (G(L/K)_[(Int.ceil u)].comap (Lift_Galois_ValEquiv K L)) ⊔ H
#check H.subgroupOf ((G(L/K)_[(Int.ceil u)].comap (Lift_Galois_ValEquiv K L)) ⊔ H)
#check ((Lift_Galois_ValEquiv K L) t)
#check i_[L/K] ((Lift_Galois_ValEquiv K L) t)
#check (fun (t : ((mk' H)⁻¹' {(Galois_to_Quotient K L σ)})) => i_[L/K] ((Lift_Galois_ValEquiv K L) t))
#check (i_[L/K] '' ((Lift_Galois_ValEquiv K L) '' ((mk' H)⁻¹' {(Galois_to_Quotient K L σ)})))
#check sSup (i_[L/K] '' ((Lift_Galois_ValEquiv K L) '' ((mk' H)⁻¹' {(Galois_to_Quotient K L σ)})))

--prop 15
theorem varphi_comp_field_ext : (varphi K (fixedField H)) ∘ (varphi (fixedField H) L) = varphi K L:= by sorry

theorem psi_comp_field_ext : (psi K K') ∘ (psi K' L) = psi K L:= by sorry

-/

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [ValAlgebra R S] (x : ℚ)
#check Int.ceil
#check φ_[L/K] x
#check ψ_[L/K] x

theorem phi_comp_field_ext : (phi K' L) ∘ (phi K K') = phi K L := by sorry

theorem psi_comp_field_ext : (psi K K') ∘ (psi K' L) = psi K L := by sorry

-- aux construction of upper numbering ramification group, correct for finite extension of local fields only. later we define a more general version on all algebraic extensions of local fields.
def upperRamificationGroup_aux (u : ℚ): (Subgroup (S ≃ₐv[R] S)) := lowerRamificationGroup R S ⌈ψ_[S/R] u⌉

scoped [Valued] notation:max " G(" L:max "/" K:max ")^[" u:max "] " => upperRamificationGroup_aux K L u

end

section

open DiscreteValuation

variable {K L : Type*} {ΓK : outParam Type*} [Field K] [Field L] [vK : Valued K ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK.v] [IsDiscrete vL.v] [ValAlgebra K L] {H : Subgroup (L ≃ₐ[K] L)} [Subgroup.Normal H] {K' : IntermediateField K L}

#synth Valued K' ℤₘ₀

#check valuedIntermediateField

variable (v : ℚ)
#check (G(L/K)^[v]).subgroupOf (H.comap ValAlgEquiv.toAlgEquivₘ)

#check AlgEquiv.restrictNormalHom

variable (K') in
def ValAlgEquiv.restrictNormalHom : (L ≃ₐv[K] L) →* K' ≃ₐv[K] K' := sorry

theorem herbrand' [Normal K K'] (v : ℚ) : G(K'/K)^[v] = G(L/K)^[v].map (ValAlgEquiv.restrictNormalHom K'):= by sorry

end
