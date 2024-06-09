import RamificationGroup.LowerNumbering
import Mathlib.RingTheory.Valuation.Basic
import RamificationGroup.Valuation.Trash.test

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

theorem psi_comp_field_ext : (psi K (fixedField H)) ∘ (psi (fixedField H) L) = psi K L:= by sorry


variable {H1 H2: Subgroup ((L ≃ₐ[K] L))}
#check H1 ⊔ H2
