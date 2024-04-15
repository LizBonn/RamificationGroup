import RamificationGroup.LowerNumbering
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.FieldTheory.KrullTopology
import RamificationGroup.HerbrandFunction
import RamificationGroup.Valued.Hom.Discrete'

/-!

## TODO
rename theorems into UpperRamificationGroup.xxx
-/

open QuotientGroup IntermediateField DiscreteValuation Valued Valuation
open HerbrandFunction


section upperRamificationGroup_aux

section definition_aux
-- principle : first try to state a theorem in IsScalarTower, then try IntermediateField
variable {K L : Type*} {ΓK : outParam Type*} [Field K] [Field L] [LinearOrderedCommGroupWithZero ΓK] [vK : Valued K ΓK] [vL : Valued L ℤₘ₀] [Algebra K L]

variable {K' : Type*} [Field K'] [vK' : Valued K' ℤₘ₀] [Algebra K K'] [Algebra K L] [Algebra K' L] [IsScalarTower K K' L] [IsValExtension K' L] -- `I hope this is enough`

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [Algebra R S] (x : ℚ)
#check Int.ceil

-- aux construction of upper numbering ramification group, correct for finite extension of local fields only. later we define a more general version on all algebraic extensions of local fields.

noncomputable def upperRamificationGroup_aux (v : ℚ): (Subgroup (S ≃ₐ[R] S)) := lowerRamificationGroup R S ⌈psi R S v⌉

end definition_aux

local notation:max " G(" L:max "/" K:max ")^[" v:max "] " => upperRamificationGroup_aux K L v

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
theorem exist_truncatedLowerIndex_eq_truncatedJ (u : ℚ) (σ : K' ≃ₐ[K] K') : ∃ s : L ≃ₐ[K] L, s ∈ (AlgEquiv.restrictNormalHom K')⁻¹' {σ} ∧  AlgEquiv.truncatedLowerIndex K L u s = HerbrandFunction.truncatedJ L u σ := by
  simp
  unfold truncatedJ
  sorry


variable {σ : K' ≃ₐ[K] K'}

#check exist_truncatedLowerIndex_eq_truncatedJ 1 σ

theorem phi_truncatedJ_sub_one (u : ℚ) (σ : K' ≃ₐ[K] K') : phi K' L ((truncatedJ L u σ) - 1) = σ.truncatedLowerIndex K K' ((phi K' L (u-1)) + 1) - 1:= by sorry

#check FiniteDimensional K L
#check FiniteDimensional K K'

theorem mem_lowerRamificationGroup_of_le_truncatedJ_sub_one {u r : ℚ} (h : u ≤ truncatedJ L r σ - 1) : σ ∈ (G(L/K)_[⌈u⌉].map (AlgEquiv.restrictNormalHom K')) := by
  simp only [Subgroup.mem_map]
  obtain ⟨s, s_in, hs⟩ := exist_truncatedLowerIndex_eq_truncatedJ (L := L) r σ
  simp at s_in
  have hs : s ∈ G(L/K)_[⌈u⌉] := by
    apply mem_lowerRamificationGroup_of_le_truncatedLowerIndex_sub_one
    rw [hs]
    linarith [h]
  use s

theorem le_truncatedJ_sub_one_iff_mem_lowerRamificationGroup {u : ℚ} {r : ℚ} (h : u + 1 ≤ r) : u ≤ truncatedJ L r σ - 1 ↔ σ ∈ (G(L/K)_[⌈u⌉].map (AlgEquiv.restrictNormalHom K')) := by
  constructor
  · apply mem_lowerRamificationGroup_of_le_truncatedJ_sub_one
  · --simp only [Subgroup.mem_map]
    rintro hx
    obtain ⟨s, s_in, hs⟩ := exist_truncatedLowerIndex_eq_truncatedJ (L := L) r σ
    simp at s_in
    let f : (L ≃ₐ[K'] L) → (AlgEquiv.restrictNormalHom K')⁻¹' {σ} :=
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
    have hi : ∀ x : (L ≃ₐ[K'] L), AlgEquiv.truncatedLowerIndex K' L u x = AlgEquiv.truncatedLowerIndex K L u (f x) := sorry -- u need to change
    have hs' : s ∈ G(L/K)_[⌈u⌉] := by
      sorry
    sorry
    --rw [← hs]
    --apply (le_truncatedLowerIndex_sub_one_iff_mem_lowerRamificationGroup s u r h).2 hs'

-- Lemma 5
@[simp]
theorem herbrand (u : ℚ) : G(L/K)_[⌈u⌉].map (AlgEquiv.restrictNormalHom K') = G(K'/K)_[⌈phi K' L u⌉] := by
  ext σ
  calc
  _ ↔ truncatedJ L (u + 1) σ - 1 ≥ u :=
  sorry
  --(le_truncatedJ_sub_one_iff_mem_lowerRamificationGroup (by linarith)).symm
  _ ↔ phi K' L (truncatedJ L (u + 1) σ - 1) ≥ phi K' L u := (phi_strictMono K' L).le_iff_le.symm
  _ ↔ σ.truncatedLowerIndex K K' ((phi K' L u) + 1) - 1 ≥ phi K' L u := by
    simp [phi_truncatedJ_sub_one]
  _ ↔ σ ∈ G(K'/K)_[⌈phi K' L u⌉] := by
    apply le_truncatedLowerIndex_sub_one_iff_mem_lowerRamificationGroup σ (phi K' L u) _
    linarith


namespace HerbrandFunction

variable {K K' L : Type*} {ΓK : outParam Type*} [Field K] [Field K'] [Field L] [vK' : Valued K' ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK'.v] [IsDiscrete vL.v] [Algebra K L] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L] [IsValExtension K' L] [Normal K K'] [Normal K L] [FiniteDimensional K L] [FiniteDimensional K K']

-- Prop 15
@[simp]
theorem phi_comp : (phi K K') ∘ (phi K' L) = phi K L := by
  ext u
  sorry

@[simp]
theorem phi_phi (u : ℚ): (phi K K') ((phi K' L) u) = (phi K L) u := by
  sorry

--Prop 15
@[simp]
theorem psi_comp : (psi K' L) ∘ (psi K K') = psi K L := by
  ext v
  sorry

@[simp]
theorem psi_psi (v : ℚ) : (psi K' L) ((psi K K') v) = psi K L v := by
  sorry

end HerbrandFunction

@[simp]
theorem UpperRamificationGroup_aux.map_restrictNormalHom (v : ℚ) : G(L/K)^[v].map (AlgEquiv.restrictNormalHom K') = G(K'/K)^[v] := by
  calc
    _ = G(L/K)_[⌈psi K L v⌉].map (AlgEquiv.restrictNormalHom K') := rfl
    _ = G(K'/K)_[⌈phi K' L (psi K L v)⌉] := herbrand _
    _ = G(K'/K)^[v] := by
      rw [← psi_comp (K' := K') (L := L)]
      simp only [Function.comp_apply, phi_psi_eq_self]
      rfl

end

section ExhausiveSeperated

variable {R : Type*} {R' S: Type*} {ΓR ΓS ΓA ΓB : outParam Type*} [CommRing R] [CommRing R'] [Ring S]
[vS : Valued S ℤₘ₀] [Algebra R S] [Algebra R R'] [Algebra R' S] [IsScalarTower R R' S]

theorem UpperRamificationGroup_aux.eq_decompositionGroup {v : ℚ} (h : v ≤ -1) :
G(S/R)^[v] = decompositionGroup R S := by
  simp only [upperRamificationGroup_aux]
  rw [psi_eq_self_of_le_neg_one R S (by linarith [h])]
  apply lowerRamificationGroup_eq_decompositionGroup
  rw [Int.ceil_le]
  exact_mod_cast h

section

variable {K L : Type*} [Field K] [Field L] [vK : Valued K ℤₘ₀] [vL : Valued L ℤₘ₀] [Algebra K L]

theorem UpperRamificationGroup_aux.eq_top [IsValExtension K L] [CompleteSpace K] {v : ℚ} (h : v ≤ -1) : G(L/K)^[v] = ⊤ := by
  rw [UpperRamificationGroup_aux.eq_decompositionGroup h, decompositionGroup_eq_top]

end

section

variable {K L : Type*} [Field K] [Field L] [vK : Valued K ℤₘ₀]  [vL : Valued L ℤₘ₀] [Algebra K L] [FiniteDimensional K L]

-- this uses local fields and bichang's work, check if the condition is too strong...
theorem UpperRamificationGroup_aux.exist_eq_bot [LocalField K] [LocalField L] [IsValExtension K L] : ∃ v : ℚ, G(L/K)^[v] = ⊥ := by
  obtain ⟨u, hu⟩ := exist_lowerRamificationGroup_eq_bot (K := K) (L := L)
  use ⌈phi K L u⌉
  simp [upperRamificationGroup_aux]
  sorry


end

end ExhausiveSeperated

end upperRamificationGroup_aux

section upperRamificationGroup
-- need a set up that every intermidiate field has a valued instance. in the cdvf case, this is possible.

-- Is this instance ok? it is possible to avoid instance and always use def, but I do think a scoped instance make statements much easier.

namespace DiscreteValuation

variable {K L : Type*} [Field K] [vK : Valued K ℤₘ₀] [Field L] [Algebra K L] [IsDiscrete vK.v] [CompleteSpace K] {K' : IntermediateField K L} [FiniteDimensional K K']

noncomputable instance valuedIntermediateField : Valued K' ℤₘ₀ := DiscreteValuation.Extension.valued K K'

/- -- success
#synth IsDiscrete (valuedIntermediateField.v : Valuation K' _)
-/

-- this is needed, or #synth CompleteSpace K' fails
instance (priority := 100) : CompleteSpace K' := DiscreteValuation.Extension.completeSpace K K'

end DiscreteValuation

/-
noncomputable def upperRamificationGroup (v : ℚ) : Subgroup (L ≃ₐ[K] L) :=
  iInf (fun F : {K' : IntermediateField K L // Normal K K' ∧ FiniteDimensional K K'} =>
  letI : Normal K F := F.property.1
  letI : FiniteDimensional K F := F.property.2
  (upperRamificationGroup_aux K (F : IntermediateField K L) v).comap (AlgEquiv.restrictNormalHom F))

#check upperRamificationGroup
-/

-- this is easier to use
noncomputable def upperRamificationGroup (K L : Type*) [Field K] [vK : Valued K ℤₘ₀] [Field L] [Algebra K L] [IsDiscrete vK.v] [CompleteSpace K] (v : ℚ) : Subgroup (L ≃ₐ[K] L) where
  carrier := {s | ∀ (F : IntermediateField K L) [Normal K F] [FiniteDimensional K F],
      s.restrictNormal F ∈ upperRamificationGroup_aux K F v}
  mul_mem' {s} {s'} hs hs' F _ _ := by
    rw [show (s * s').restrictNormal F = s.restrictNormal F * s'.restrictNormal F by
        exact (AlgEquiv.restrictNormalHom F).map_mul s s']
    exact Subgroup.mul_mem (upperRamificationGroup_aux K F v) (hs F) (hs' F)
  one_mem' F _ _ := by
    rw [show AlgEquiv.restrictNormal 1 F = (1 : F ≃ₐ[K] F) by
        exact (AlgEquiv.restrictNormalHom F).map_one]
    exact Subgroup.one_mem (upperRamificationGroup_aux K F v)
  inv_mem' {s} hs F _ _ := by
    rw [show AlgEquiv.restrictNormal s⁻¹ F = (AlgEquiv.restrictNormal s F)⁻¹ by
        exact (AlgEquiv.restrictNormalHom F).map_inv s]
    exact Subgroup.inv_mem (upperRamificationGroup_aux K F v) (hs F)

#check upperRamificationGroup

scoped [Valued] notation:max " G(" L:max "/" K:max ")^[" v:max "] " => upperRamificationGroup K L v

namespace UpperRamificationGroup

variable {K L : Type*} [Field K] [vK : Valued K ℤₘ₀] [Field L] [Algebra K L] [IsDiscrete vK.v] [CompleteSpace K]

-- theorem relation with aux
theorem eq_UpperRamificationGroup_aux [vL : Valued L ℤₘ₀] [IsDiscrete vL.v] [IsValExtension K L] [FiniteDimensional K L] (v : ℚ) : upperRamificationGroup K L v = upperRamificationGroup_aux K L v := sorry

theorem mem_iff_mem_UpperRamificationGroup_aux {s : L ≃ₐ[K] L} {v : ℚ} : s ∈ G(L/K)^[v] ↔ ∀ (F : IntermediateField K L) [Normal K F] [FiniteDimensional K F],
      s.restrictNormal F ∈ upperRamificationGroup_aux K F v := by
  rfl

-- theorem compatible with quotient, finite quotient
@[simp]
theorem map_restrictNormalHom {K'} [Field K'] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L] [Normal K K'] (v : ℚ) : G(L/K)^[v].map (AlgEquiv.restrictNormalHom K') = G(K'/K)^[v] := sorry

theorem mem_iff {s : L ≃ₐ[K] L} {v : ℚ} : s ∈ G(L/K)^[v] ↔ ∀ (F : IntermediateField K L) [Normal K F] [FiniteDimensional K F],
      s.restrictNormal F ∈ G(F/K)^[v] := by
  conv =>
    rhs
    intro F i i'
    rhs
    rw [(eq_UpperRamificationGroup_aux (K := K) (L := F) v)]

-- theorems about exhausive and separated
-- under what condition this is correct? this is too strong?
theorem eq_decompositionGroup [vL : Valued L ℤₘ₀] [IsDiscrete vL.v] [IsValExtension K L] [FiniteDimensional K L] {v : ℚ} (h : v ≤ -1) :
G(L/K)^[v] = decompositionGroup K L := by
  rw [eq_UpperRamificationGroup_aux]
  exact UpperRamificationGroup_aux.eq_decompositionGroup h

theorem eq_top [vL : Valued L ℤₘ₀] [IsDiscrete vL.v] [IsValExtension K L] [FiniteDimensional K L] {v : ℚ} (h : v ≤ -1) : G(L/K)^[v] = ⊤ := by
  rw [eq_UpperRamificationGroup_aux]
  exact UpperRamificationGroup_aux.eq_top h

end UpperRamificationGroup

namespace UpperRamificationGroup

variable {K L : Type*} [Field K] [Field L] [vK : Valued K ℤₘ₀]  [vL : Valued L ℤₘ₀] [IsDiscrete vK.v] [CompleteSpace K] [Algebra K L] [FiniteDimensional K L] [LocalField K] [LocalField L] [IsValExtension K L]

theorem inf_eq_bot (s : L ≃ₐ[K] L) : ∀ v, s ∈ G(L/K)^[v] ↔ s = 1 := sorry


/-
-- For apf extensions, theorem relation with Krull topology (?) top bases(how to state this ??)
-- this theorem dont need so much hyp
theorem isOpen {v : ℚ} : IsOpen (G(L/K)^[v] : Set (L ≃ₐ[K] L)) := sorry

-- should add `galNormalBasis` to Mathlib first, maybe just leave it later
def basis : GroupFilterBasis (L ≃ₐ[K] L) := sorry
-/

end UpperRamificationGroup




end upperRamificationGroup
