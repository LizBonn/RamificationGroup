import RamificationGroup.LowerNumbering
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.FieldTheory.KrullTopology
import RamificationGroup.HerbrandFunction
import RamificationGroup.Valued.Hom.Discrete'

open QuotientGroup IntermediateField DiscreteValuation Valued Valuation
open HerbrandFunction

/-
namespace ValAlgEquiv
#check AlgEquiv.restrictNormalHom
variable {K L} (K') {ΓK ΓK' ΓL : outParam Type*} [Field K] [Field K'] [Field L]
[LinearOrderedCommGroupWithZero ΓK]
[LinearOrderedCommGroupWithZero ΓK']
[LinearOrderedCommGroupWithZero ΓL]
[vK : Valued K ΓK] [vK' : Valued K' ΓK'] [vL : Valued L ΓL]
[Algebra K K'] [Algebra K L] [Algebra K' L] [IsScalarTower K K' L] [Normal K K']
-- change this using IsScalatower
open algebraMap

theorem restrictNormalHom.val_isEquiv_comap_aux (f : (L ≃ₐ[K] L)): vK'.v.IsEquiv (vK'.v.comap (AlgEquiv.restrictNormalHom K' (f : L ≃ₐ[K] L)))  := by
  intro x y
  convert f.val_isEquiv_comap' (x : L) (y : L)
  simp only [ValAlgebra.val_map_le_iff]
  dsimp
  rw [← ValAlgebra.val_map_le_iff (A := L), iff_eq_eq]
  congr <;>
  calc
    _ = f _ := AlgEquiv.restrictNormal_commutes (f : L ≃ₐ[K] L) K' _
    _ = _ := rfl

noncomputable def restrictNormalHom : (L ≃ₐv[K] L) →* K' ≃ₐv[K] K' where
  toFun f :=
    {
      AlgEquiv.restrictNormalHom K' (f : L ≃ₐ[K] L) with
      val_isEquiv_comap' := restrictNormalHom.val_isEquiv_comap_aux K' f
      map_le_map_iff' := map_le_map_iff_of_val_isEquiv_comap (restrictNormalHom.val_isEquiv_comap_aux K' f)
      continuous_toFun := sorry
      continuous_invFun := sorry
    }
  map_one' := by
    ext a
    calc
      _ = ((AlgEquiv.restrictNormalHom K') (.refl : L ≃ₐ[K] L)) a := rfl
      _ = _ := by
        erw [_root_.map_one]
        rfl
  map_mul' s s' := by
    ext a
    calc
      _ = (AlgEquiv.restrictNormalHom K' (s * s' : L ≃ₐ[K] L)) a := rfl
      _ = ((AlgEquiv.restrictNormalHom K' (s : L ≃ₐ[K] L)) * (AlgEquiv.restrictNormalHom K' (s' : L ≃ₐ[K] L))) a := by
        erw [_root_.map_mul]
      _ = _ := rfl


theorem restrictNormalHom_surjective : Function.Surjective (restrictNormalHom K' (K := K) (L := L)) := by
  rintro a
  sorry

end ValAlgEquiv

-/

section

-- principle : first try to state a theorem in IsScalarTower, then try IntermediateField
variable {K L : Type*} {ΓK : outParam Type*} [Field K] [Field L] [LinearOrderedCommGroupWithZero ΓK] [vK : Valued K ΓK] [vL : Valued L ℤₘ₀] [Algebra K L]

variable {K' : Type*} [Field K'] [vK' : Valued K' ℤₘ₀] [Algebra K K'] [Algebra K L] [Algebra K' L] [IsScalarTower K K' L] [IsValExtension K' L] -- `I hope this is enough`

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [Algebra R S] (x : ℚ)
#check Int.ceil

-- aux construction of upper numbering ramification group, correct for finite extension of local fields only. later we define a more general version on all algebraic extensions of local fields.
noncomputable def upperRamificationGroup_aux (v : ℚ): (Subgroup (S ≃ₐ[R] S)) := lowerRamificationGroup R S ⌈psi R S v⌉

scoped [Valued] notation:max " G(" L:max "/" K:max ")^[" u:max "] " => upperRamificationGroup_aux K L u

end

section

open DiscreteValuation

variable {K K' L : Type*} {ΓK : outParam Type*} [Field K] [Field K'] [Field L] [vK' : Valued K' ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK'.v] [IsDiscrete vL.v] [Algebra K L] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L] [IsValExtension K' L] [Normal K K'] [Normal K L] [FiniteDimensional K L] [FiniteDimensional K K']

variable (σ : K' ≃ₐ[K] K')

open Classical
-- Lemma 4
theorem preimage_singleton_nonempty {σ : K' ≃ₐ[K] K'} : ((AlgEquiv.restrictNormalHom K' (K₁ := L))⁻¹' {σ}).toFinset.Nonempty := by
  apply Finset.coe_nonempty.mp
  simp only [Set.coe_toFinset]
  exact Set.Nonempty.preimage (Set.singleton_nonempty _) (AlgEquiv.restrictNormalHom_surjective (F := K) (E := L) (K₁ := K'))

variable (L) in
noncomputable def HerbrandFunction.truncatedJ (u : ℚ) (σ : K' ≃ₐ[K] K') : ℚ := Finset.max' (((AlgEquiv.restrictNormalHom K')⁻¹' {σ}).toFinset.image (fun (x : L ≃ₐ[K] L) => x.truncatedLowerIndex K L u - 1)) (Finset.Nonempty.image preimage_singleton_nonempty _)


#check Finset.max'_mem
#check Finset.max'_image
theorem exist_truncatedLowerIndex_eq_truncatedJ (u : ℚ) (σ : K' ≃ₐ[K] K') : ∃ s : L ≃ₐ[K] L, s ∈ (ValAlgEquiv.restrictNormalHom K')⁻¹' {σ} ∧  ValAlgEquiv.truncatedLowerIndex K L u s = HerbrandFunction.truncatedJ u σ := by
  simp
  unfold truncatedJ
  sorry

variable {σ : K' ≃ₐ[K] K'}

theorem phi_truncatedJ_sub_one (u : ℚ) (σ : K' ≃ₐ[K] K') : phi K' L ((truncatedJ L u σ) - 1) = σ.truncatedLowerIndex K K' ((phi K' L (u-1)) + 1) - 1:= by sorry

theorem mem_lowerRamificationGroup_of_le_truncatedJ_sub_one {u r : ℚ} (h : u ≤ truncatedJ r σ - 1) : σ ∈ (G(L/K)_[⌈u⌉].map (ValAlgEquiv.restrictNormalHom K')) := by
  simp only [Subgroup.mem_map]
  obtain ⟨s, s_in, hs⟩ := exist_truncatedLowerIndex_eq_truncatedJ r σ
  simp at s_in
  have hs : s ∈ G(L/K)_[⌈u⌉] := by
    apply mem_lowerRamificationGroup_of_le_truncatedLowerIndex_sub_one
    rw [hs]
    linarith [h]
  use s

theorem le_truncatedJ_sub_one_iff_mem_lowerRamificationGroup {u : ℚ} {r : ℚ} (h : u + 1 ≤ r) : u ≤ truncatedJ r σ - 1 ↔ σ ∈ (G(L/K)_[⌈u⌉].map (ValAlgEquiv.restrictNormalHom K')) := by
  constructor
  · apply mem_lowerRamificationGroup_of_le_truncatedJ_sub_one
  · --simp only [Subgroup.mem_map]
    rintro hx
    obtain ⟨s, s_in, hs⟩ := exist_truncatedLowerIndex_eq_truncatedJ r σ
    simp at s_in
    let f : (L ≃ₐ[K'] L) → (ValAlgEquiv.restrictNormalHom K')⁻¹' {σ} :=
      fun x => ⟨s * (x.restrictScalars K), by
        simp [s_in]
        sorry⟩
        --apply ValAlgEquiv.resNormal_of_resScalar_eq_refl⟩
    have hbij : Function.Bijective f := by
      constructor
      · rintro a1 a2 h
        simp [f] at h
        sorry
      · rintro b
        sorry
    have hi : ∀ x : (L ≃ₐ[K'] L), ValAlgEquiv.truncatedLowerIndex K' L u x = ValAlgEquiv.truncatedLowerIndex K L u (f x) := sorry -- u need to change
    have hs' : s ∈ G(L/K)_[⌈u⌉] := by
      sorry
    rw [← hs]
    apply (le_truncatedLowerIndex_sub_one_iff_mem_lowerRamificationGroup s u r h).2 hs'

-- Lemma 5
@[simp]
theorem herbrand (u : ℚ) : G(L/K)_[⌈u⌉].map (AlgEquiv.restrictNormalHom K') = G(K'/K)_[⌈phi K' L u⌉] := by
  ext σ
  calc
  _ ↔ truncatedJ L (u + 1) σ - 1 ≥ u := (le_truncatedJ_sub_one_iff_mem_lowerRamificationGroup (by linarith)).symm
  _ ↔ phi K' L (truncatedJ L (u + 1) σ - 1) ≥ phi K' L u := (phi_strictMono K' L).le_iff_le.symm
  _ ↔ σ.truncatedLowerIndex K K' ((phi K' L u) + 1) - 1 ≥ phi K' L u := by
    simp [phi_truncatedJ_sub_one]
  _ ↔ σ ∈ G(K'/K)_[⌈phi K' L u⌉] := by
    apply le_truncatedLowerIndex_sub_one_iff_mem_lowerRamificationGroup σ (phi K' L u) _
    linarith


@[simp]
theorem herbrand' (v : ℚ) : G(L/K)^[v].map (AlgEquiv.restrictNormalHom K') = G(K'/K)^[v] := by
  calc
    _ = G(L/K)_[⌈psi K L v⌉].map (AlgEquiv.restrictNormalHom K') := rfl
    _ = G(K'/K)_[⌈phi K' L (psi K L v)⌉] := herbrand _
    _ = G(K'/K)^[v] := by
      sorry
      -- rw [← psi_comp_of_isValExtension (K' := K') (L := L)]
      -- simp only [Function.comp_apply, phi_psi_eq_self]
      -- rfl

end

namespace HerbrandFunction

variable {K K' L : Type*} {ΓK : outParam Type*} [Field K] [Field K'] [Field L] [vK' : Valued K' ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK'.v] [IsDiscrete vL.v] [Algebra K L] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L] [IsValExtension K' L] [Normal K K'] [Normal K L] [FiniteDimensional K L] [FiniteDimensional K K']

-- Prop 15
@[simp]
theorem phi_comp_of_isValExtension : (phi K K') ∘ (phi K' L) = phi K L := by
  ext u
  sorry

@[simp]
theorem phi_comp_of_isValExtension' (u : ℚ): (phi K K') ((phi K' L) u) = (phi K L) u := by
  sorry

--Prop 15
@[simp]
theorem psi_comp_of_isValExtension : (psi K' L) ∘ (psi K K') = psi K L := by
  ext v
  sorry

@[simp]
theorem psi_comp_of_isValExtension' (v : ℚ) : (psi K' L) ((psi K K') v) = psi K L v := by
  sorry

end HerbrandFunction

/-
variable (K L) [Field K] [Field L] {ΓL : outParam Type*} [LinearOrderedCommGroupWithZero ΓL] [vK : Valued K ℤₘ₀] [vL : Valued L ΓL] [ValAlgebra K L] {E : IntermediateField K L}

variable {K L} in
def discreteValuedOfFinite : Valued E ℤₘ₀ := sorry

variable {K L} in
def valAlgebraOfFinite : ValAlgebra K (A := E) (vA := discreteValuedOfFinite) := sorry
variable {K L} in
def valAlgebraOfFinite' : ValAlgebra (R := E) L (vR := discreteValuedOfFinite) := sorry

def upperRamificationGroup (v : ℚ): (Subgroup (L ≃ₐv[K] L)) where
  carrier := { s | ∀ E ∈ finiteExts K L,
    letI : Valued E ℤₘ₀ := discreteValuedOfFinite;
    letI : ValAlgebra K E := valAlgebraOfFinite
    letI : ValAlgebra E L := valAlgebraOfFinite'
    Normal K E → (ValAlgEquiv.restrictNormalHom (K' := E) s ∈ G(E/K)^[v]) }
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

/-
theorem upperRamificationGroup compatible with quotient

theorem upperRamificationGroup = upperRamificationGroup_aux in finite case

-/

#check finiteExts
#check fixedByFinite
-/
