import RamificationGroup.LowerNumbering
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.FieldTheory.KrullTopology
import RamificationGroup.HerbrandFunction
import Mathlib.Algebra.Algebra.Tower
-- import RamificationGroup.Valued.Hom.Discrete'

/-!

## TODO
rename theorems into UpperRamificationGroup.xxx
-/

open QuotientGroup IntermediateField DiscreteValuation Valued Valuation
open HerbrandFunction

noncomputable
section

section upperRamificationGroup_aux

section definition_aux
-- principle : first try to state a theorem in IsScalarTower, then try IntermediateField
variable {K L : Type*} {ΓK : outParam Type*} [Field K] [Field L] [LinearOrderedCommGroupWithZero ΓK] [vK : Valued K ΓK] [vL : Valued L ℤₘ₀] [Algebra K L]

variable {K' : Type*} [Field K'] [vK' : Valued K' ℤₘ₀] [Algebra K K'] [Algebra K L] [Algebra K' L] [IsScalarTower K K' L] [IsValExtension K' L] -- `I hope this is enough`

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [Algebra R S]

-- aux construction of upper numbering ramification group, correct for finite extension of local fields only. later we define a more general version on all algebraic extensions of local fields.

def upperRamificationGroup_aux (v : ℚ): (Subgroup (S ≃ₐ[R] S)) := lowerRamificationGroup R S ⌈psi R S v⌉

end definition_aux

local notation:max " G(" L:max "/" K:max ")^[" v:max "] " => upperRamificationGroup_aux K L v

section autCongr

variable {K L L': Type*} {ΓK : outParam Type*} [Field K] [Field L] [Field L'] [vL : Valued L ℤₘ₀] [vL' : Valued L' ℤₘ₀] [IsDiscrete vL.v] [IsDiscrete vL'.v] [Algebra K L] [Algebra K L']

theorem autCongr_mem_upperRamificationGroup_aux_iff {f : L ≃ₐ[K] L'} (hf : ∀ a : L, v a = v (f a)) (s : L ≃ₐ[K] L) (v : ℚ) : s ∈ G(L/K)^[v] ↔ (AlgEquiv.autCongr f s : L' ≃ₐ[K] L') ∈ G(L'/K)^[v] := by
  convert autCongr_mem_lowerRamificationGroup_iff hf s ⌈psi K L v⌉
  simp only [upperRamificationGroup_aux]
  congr 2
  exact (psi_eq_ofEquiv _ _ _ hf v).symm


end autCongr


section

open DiscreteValuation

variable {K K' L : Type*} {ΓK : outParam Type*} [Field K] [Field K'] [Field L] [vK' : Valued K' ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK'.v] [IsDiscrete vL.v] [Algebra K L] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L] [IsValExtension K' L] [Normal K K'] [Normal K L] [FiniteDimensional K L] [FiniteDimensional K K'] [FiniteDimensional K' L]

variable (σ : K' ≃ₐ[K] K')

open Classical
-- Lemma 4
theorem preimage_singleton_nonempty {σ : K' ≃ₐ[K] K'} : ((AlgEquiv.restrictNormalHom K' (K₁ := L))⁻¹' {σ}).toFinset.Nonempty := by
  apply Finset.coe_nonempty.mp
  simp only [Set.coe_toFinset]
  exact Set.Nonempty.preimage (Set.singleton_nonempty _) (AlgEquiv.restrictNormalHom_surjective (F := K) (E := L) (K₁ := K'))

variable (L) in
def HerbrandFunction.truncatedJ (u : ℚ) (σ : K' ≃ₐ[K] K') : ℚ := Finset.max' (((AlgEquiv.restrictNormalHom K')⁻¹' {σ}).toFinset.image (fun (x : L ≃ₐ[K] L) => x.truncatedLowerIndex K L u - 1)) (Finset.Nonempty.image preimage_singleton_nonempty _)


theorem exist_truncatedLowerIndex_eq_truncatedJ (u : ℚ) (σ : K' ≃ₐ[K] K') : ∃ s : L ≃ₐ[K] L, s ∈ (AlgEquiv.restrictNormalHom K')⁻¹' {σ} ∧  AlgEquiv.truncatedLowerIndex K L u s - 1 = HerbrandFunction.truncatedJ L u σ := by
  have hnem : ((AlgEquiv.restrictNormalHom K' (K₁ := L))⁻¹' {σ}).Nonempty := by
    have h1 : Set.SurjOn (AlgEquiv.restrictNormalHom K' (K₁ := L)) ((AlgEquiv.restrictNormalHom K' (K₁ := L))⁻¹' {σ}) {σ} := by
      simp
      sorry
    apply Set.SurjOn.comap_nonempty h1 (by simp)
  --i'm not sure this condition below is satisfy in our sugestion.If the extension is finite, this proof make sense.
  have hfin : Finite ((AlgEquiv.restrictNormalHom K' (K₁ := L))⁻¹' {σ}) := by sorry
  obtain ⟨s, hs⟩ := Set.exists_max_image ((AlgEquiv.restrictNormalHom K' (K₁ := L))⁻¹' {σ}) (fun x => AlgEquiv.truncatedLowerIndex K L u x - 1) hfin hnem
  use s
  rcases hs with ⟨hs1, hs2⟩
  constructor
  · exact hs1
  · unfold truncatedJ
    apply le_antisymm
    · apply Finset.le_max'
      apply Finset.mem_image.2
      use s
      constructor
      apply Set.mem_toFinset.2 hs1; rfl
    · have hnem' : (((AlgEquiv.restrictNormalHom K')⁻¹' {σ}).toFinset.image (fun (x : L ≃ₐ[K] L) => x.truncatedLowerIndex K L u - 1)).Nonempty := by
        apply Finset.Nonempty.image
        apply Set.toFinset_nonempty.2 hnem
      apply (Finset.max'_le_iff (((AlgEquiv.restrictNormalHom K')⁻¹' {σ}).toFinset.image (fun (x : L ≃ₐ[K] L) => x.truncatedLowerIndex K L u - 1)) hnem').2
      intro y hy
      have hy1 : ∃ b ∈ (AlgEquiv.restrictNormalHom K') ⁻¹' {σ}, i_[L/K]ₜ u b - 1 = y := by
        convert Finset.mem_image.1 hy
        apply Set.mem_toFinset.symm
      obtain ⟨b, hb1, hb2⟩ := hy1
      rw [← hb2]
      apply hs2
      exact hb1


variable {σ : K' ≃ₐ[K] K'}

#check exist_truncatedLowerIndex_eq_truncatedJ 1 σ
--they should in lower
--theorem prop2_aux {t : L ≃ₐ[K'] L} : i_[L/K] (t.restrictScalars K) = i_[L/K'] t := by
  --sorry

theorem lemma3_aux (u : ℚ) : σ.truncatedLowerIndex K K' ((phi K' L (u-1)) + 1) = (1 / LocalField.ramificationIdx K' L) * (∑ s in (⊤ : Finset (L ≃ₐ[K'] L)), (AlgEquiv.truncatedLowerIndex K L (truncatedJ L u σ) (AlgEquiv.restrictScalars K s))) := by
  sorry

theorem RamificationIdx_eq_card_of_inertia_group : (Nat.card G(L/K')_[0]) = (LocalField.ramificationIdx K' L) := by
  sorry

theorem phi_truncatedJ_sub_one (u : ℚ) (σ : K' ≃ₐ[K] K') : phi K' L ((truncatedJ L u σ) - 1) + 1 = σ.truncatedLowerIndex K K' ((phi K' L (u-1)) + 1) := by
  obtain ⟨s, hs1, hs2⟩ :=  exist_truncatedLowerIndex_eq_truncatedJ (K := K) (K' := K') (L := L) u σ
  calc
  _ = (1 / Nat.card G(L/K')_[0]) * ((Finset.sum (⊤ : Finset (L ≃ₐ[K'] L)) (AlgEquiv.truncatedLowerIndex K' L (truncatedJ L u σ) ·))) := by
    rw [phi_eq_sum_inf]
    simp
  _ = (1 / LocalField.ramificationIdx K' L) * ((Finset.sum (⊤ : Finset (L ≃ₐ[K'] L)) (AlgEquiv.truncatedLowerIndex K' L (truncatedJ L u σ) ·))) := by
    congr
    apply RamificationIdx_eq_card_of_inertia_group
  _ = (1 / LocalField.ramificationIdx K' L) * ((∑ x in (⊤ : Finset (L ≃ₐ[K'] L)), (AlgEquiv.truncatedLowerIndex K L (truncatedJ L u σ) (AlgEquiv.restrictScalars K x)))) := by
    congr
  _ = σ.truncatedLowerIndex K K' ((phi K' L (u-1)) + 1) := by
    rw [lemma3_aux]


variable [vK : Valued K ℤₘ₀] [IsValExtension K L] [CompleteSpace K] [IsDiscrete vK.v]

theorem mem_lowerRamificationGroup_of_le_truncatedJ_sub_one {u r : ℚ} (h : u ≤ truncatedJ L r σ) : σ ∈ (G(L/K)_[⌈u⌉].map (AlgEquiv.restrictNormalHom K')) := by
  simp only [Subgroup.mem_map]
  obtain ⟨s, s_in, hs⟩ := exist_truncatedLowerIndex_eq_truncatedJ (L := L) r σ
  simp at s_in
  have hs : s ∈ G(L/K)_[⌈u⌉] := by
    apply mem_lowerRamificationGroup_of_le_truncatedLowerIndex_sub_one (r := r)
    rw [hs]
    linarith [h]
    rw [decompositionGroup_eq_top]
    apply Subgroup.mem_top
  use s

#check AlgEquiv

theorem resNormal_resScalar_aux {x : L ≃ₐ[K'] L} : (AlgEquiv.restrictNormalHom K') (AlgEquiv.restrictScalars K x) = 1 := by sorry

#check restrictScalars_injective

theorem le_truncatedJ_sub_one_iff_mem_lowerRamificationGroup {u : ℚ} {r : ℚ} (h : u + 1 ≤ r) : u ≤ truncatedJ L r σ ↔ σ ∈ (G(L/K)_[⌈u⌉].map (AlgEquiv.restrictNormalHom K')) := by
  constructor
  · apply mem_lowerRamificationGroup_of_le_truncatedJ_sub_one
  · --simp only [Subgroup.mem_map]
    rintro hx
    obtain ⟨s, s_in, hs⟩ := exist_truncatedLowerIndex_eq_truncatedJ (L := L) r σ
    simp at s_in
    let f : (L ≃ₐ[K'] L) → (AlgEquiv.restrictNormalHom K')⁻¹' {σ} :=
      fun x => ⟨s * (x.restrictScalars K), by
        rw [Set.mem_preimage, MonoidHom.map_mul, s_in, Set.mem_singleton_iff, resNormal_resScalar_aux, mul_one]⟩
    have hbij : Function.Bijective f := by
      constructor
      · rintro a1 a2 h
        dsimp [f] at h
        have h' : s * AlgEquiv.restrictScalars K a1 = s * AlgEquiv.restrictScalars K a2 := by
          apply Subtype.val_inj.2 h
        apply mul_left_cancel at h'
        apply (AlgEquiv.restrictScalars_injective K) h'
      · rintro b
        dsimp [f]
        have h : ∃ (a : L ≃ₐ[K'] L), AlgEquiv.restrictScalars K a = s⁻¹ * b.val := by
          sorry
        obtain ⟨a, ha⟩ := h
        use a
        rw [Subtype.mk.injEq, ha, ← mul_assoc, mul_inv_self, one_mul]
    have hi : ∀ x : (L ≃ₐ[K'] L), AlgEquiv.truncatedLowerIndex K' L u x = AlgEquiv.truncatedLowerIndex K L u (f x) := sorry -- u need to change
    have hs' : s ∈ G(L/K)_[⌈u⌉] := by
      sorry
    rw [← hs]
    apply (le_truncatedLowerIndex_sub_one_iff_mem_lowerRamificationGroup s u r h).2 hs'

namespace HerbrandFunction

variable {K K' L : Type*} {ΓK : outParam Type*} [Field K] [Field K'] [Field L] [vK' : Valued K' ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK'.v] [IsDiscrete vL.v] [Algebra K L] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L] [IsValExtension K' L] [Normal K K'] [Normal K L] [FiniteDimensional K L] [FiniteDimensional K K']

-- Prop 15
open Function HerbrandFunction

@[simp]
theorem phi_comp_of_isValExtension' (u : ℚ): (phi K K') ((phi K' L) u) = (phi K L) u := by
  --this line can be simper
  rw [← comp_apply (f := (phi K K')) (g := (phi K' L)) (x := u)]
  sorry

@[simp]
theorem phi_comp_of_isValExtension : (phi K K') ∘ (phi K' L) = phi K L := by
  ext u
  exact phi_comp_of_isValExtension' u

--Prop 15


--for mathlib
@[simp]
theorem Function.comp_left_cancel {α β γ: Type*} [Nonempty α] {f1 f2 : β → γ} {g : α → β} (h : Bijective g) (h1 : f1 ∘ g = f2 ∘ g) : f1 = f2 := by
  ext x
  have hsurj : ∀ (x : β), ∃ (y : α), g y = x := by
    apply Function.Bijective.surjective h
  obtain ⟨y, hy⟩ := hsurj x
  rw [← hy, ← (Function.comp_apply (f := f1) (g := g) (x := y)), ← (Function.comp_apply (f := f2) (g := g) (x := y)), h1]


@[simp]
theorem psi_comp_of_isValExtension : (psi K' L) ∘ (psi K K') = psi K L := by
  unfold psi
  have hcomp : invFun (phi K' L) ∘ invFun (phi K K') ∘ (phi K K') ∘ (phi K' L) = invFun (phi K L) ∘ (phi K K') ∘ (phi K' L) := by
    nth_rw 2 [phi_comp_of_isValExtension]
    rw [invFun_comp (phi_Bijective K L).injective, ← comp.assoc (invFun (phi K K')) (phi K K') (phi K' L), invFun_comp (phi_Bijective K K').injective, id_comp, invFun_comp (phi_Bijective K' L).injective]
  simp [Function.comp_left_cancel (phi_Bijective K' L)] at hcomp
  apply Function.comp_left_cancel (phi_Bijective K L) hcomp

@[simp]
theorem psi_comp_of_isValExtension' (v : ℚ) : (psi K' L) ((psi K K') v) = psi K L v := by
  rw [← psi_comp_of_isValExtension (K := K) (K' := K') (L := L)]
  simp

end HerbrandFunction

variable [IsValExtension K K']

-- Lemma 5
@[simp]
theorem herbrand (u : ℚ) : G(L/K)_[⌈u⌉].map (AlgEquiv.restrictNormalHom K') = G(K'/K)_[⌈phi K' L u⌉] := by
  ext σ
  #check truncatedJ L (u + 1) σ ≥ (u + 1)
  calc
  _ ↔ truncatedJ L u σ ≥ u :=
    sorry--(le_truncatedJ_sub_one_iff_mem_lowerRamificationGroup (by linarith)).symm
  _ ↔ phi K' L (truncatedJ L u σ) ≥ phi K' L u := (phi_strictMono K' L).le_iff_le.symm
  _ ↔ σ.truncatedLowerIndex K K' ((phi K' L u) + 1) - 1 ≥ phi K' L u := by
    simp [phi_truncatedJ_sub_one]
    have heq : phi K' L (truncatedJ L (u + 1) σ) = i_[K'/K]ₜ (phi K' L u + 1) σ - 1 := by
      have heq' : phi K' L (truncatedJ L (u + 1) σ - 1) + 1 = i_[K'/K]ₜ (phi K' L u + 1) σ  := by
        simp only [phi_truncatedJ_sub_one, add_sub_cancel_right u 1]
      rw [← heq', add_sub_cancel_right _ 1]
      sorry
    rw [heq]
  _ ↔ σ ∈ G(K'/K)_[⌈phi K' L u⌉] := by
    apply le_truncatedLowerIndex_sub_one_iff_mem_lowerRamificationGroup σ (phi K' L u) _
    rw [add_le_add_iff_right]

@[simp]
theorem herbrand' (v : ℚ) : G(L/K)^[v].map (AlgEquiv.restrictNormalHom K') = G(K'/K)^[v] := by
  calc
    _ = G(L/K)_[⌈psi K L v⌉].map (AlgEquiv.restrictNormalHom K') := rfl
    _ = G(K'/K)_[⌈phi K' L (psi K L v)⌉] := herbrand _
    _ = G(K'/K)^[v] := by
      rw [← psi_comp_of_isValExtension (K' := K') (L := L)]
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

-- Should this have `[IsDiscrete vK.v]`?
theorem UpperRamificationGroup_aux.eq_top [IsValExtension K L] [CompleteSpace K] [IsDiscrete vK.v] [FiniteDimensional K L] {v : ℚ} (h : v ≤ -1) : G(L/K)^[v] = ⊤ := by
  rw [UpperRamificationGroup_aux.eq_decompositionGroup h, decompositionGroup_eq_top]

end

section

variable {K L : Type*} [Field K] [Field L] [vK : Valued K ℤₘ₀]  [vL : Valued L ℤₘ₀] [Algebra K L] [FiniteDimensional K L]


-- this uses local fields and bichang's work, check if the condition is too strong...
theorem UpperRamificationGroup_aux.exist_eq_bot [LocalField K] [LocalField L] [IsValExtension K L] : ∃ v : ℚ, G(L/K)^[v] = ⊥ := by
  -- obtain ⟨u, hu⟩ := exist_lowerRamificationGroup_eq_bot (K := K) (L := L)
  -- use ⌈phi K L u⌉
  -- simp [upperRamificationGroup_aux]
  sorry


end

end ExhausiveSeperated

end upperRamificationGroup_aux

section upperRamificationGroup
-- need a set up that every intermidiate field has a valued instance. in the cdvf case, this is possible.

-- Is this instance ok? it is possible to avoid instance and always use def, but I do think a scoped instance make statements much easier.


/-
noncomputable def upperRamificationGroup (v : ℚ) : Subgroup (L ≃ₐ[K] L) :=
  iInf (fun F : {K' : IntermediateField K L // Normal K K' ∧ FiniteDimensional K K'} =>
  letI : Normal K F := F.property.1
  letI : FiniteDimensional K F := F.property.2
  (upperRamificationGroup_aux K (F : IntermediateField K L) v).comap (AlgEquiv.restrictNormalHom F))

#check upperRamificationGroup
-/
#check Valued.toUniformSpace
theorem Valued.toUniformSpace_eq_of_v_eq {K Γ : Type*} [Ring K] [LinearOrderedCommGroupWithZero Γ] {v₁ v₂ : Valued K Γ} (h : v₁.v = v₂.v) : v₁.toUniformSpace = v₂.toUniformSpace := by
  apply UniformAddGroup.ext v₁.toUniformAddGroup v₂.toUniformAddGroup
  ext s
  rw [v₁.is_topological_valuation, v₂.is_topological_valuation, h]

def completeSpaceIsValExtension (K F : Type*) [Field K] [vK : Valued K ℤₘ₀] [IsDiscrete vK.v] [CompleteSpace K] [Field F] [vF : Valued F ℤₘ₀] [IsDiscrete vF.v] [Algebra K F] (h : vK.v.IsEquiv <| vF.v.comap (algebraMap K F)) [FiniteDimensional K F]: CompleteSpace F := by
  have veq : vF.v = extendedValuation K F := by
    rw [← isEquiv_iff_eq]
    exact extension_valuation_equiv_extendedValuation_of_discrete h
  have ueq: vF.toUniformSpace = (DiscreteValuation.Extension.valued K F).toUniformSpace := Valued.toUniformSpace_eq_of_v_eq veq
  erw [ueq]
  exact DiscreteValuation.Extension.completeSpace K F

open AlgEquiv

#check extension_valuation_equiv_extendedValuation_of_discrete
#check isEquiv_iff_eq
#check IntermediateField
#check DiscreteValuation.Extension.completeSpace
-- this is easier to use

universe u v

-- universe problem, what should be F's universe? max u v requires ULift
def upperRamificationGroup (K : Type u) (L : Type v) [Field K] [vK : Valued K ℤₘ₀] [Field L] [Algebra K L] [IsDiscrete vK.v] [CompleteSpace K] (v : ℚ) : Subgroup (L ≃ₐ[K] L) where
  carrier := {s | ∀ (F : Type v) [Field F] [vF : Valued F ℤₘ₀] [IsDiscrete vF.v] [Algebra K F] [IsValExtension K F] [Algebra F L] [IsScalarTower K F L] [Normal K F] [FiniteDimensional K F],
    restrictNormalHom F s ∈ upperRamificationGroup_aux K F v}
  mul_mem' {s} {s'} hs hs' F:= by
    intros
    rw [(restrictNormalHom F).map_mul s s']
    exact Subgroup.mul_mem (upperRamificationGroup_aux K F v) (hs F) (hs' F)
  one_mem' F := by
    intros
    rw [(restrictNormalHom F).map_one]
    exact Subgroup.one_mem (upperRamificationGroup_aux K F v)
  inv_mem' {s} hs F:= by
    intros
    rw [(restrictNormalHom F).map_inv s]
    exact Subgroup.inv_mem (upperRamificationGroup_aux K F v) (hs F)

#check upperRamificationGroup

scoped [Valued] notation:max " G(" L:max "/" K:max ")^[" v:max "] " => upperRamificationGroup K L v

namespace UpperRamificationGroup

variable {K L : Type*} [Field K] [vK : Valued K ℤₘ₀] [Field L] [Algebra K L] [IsDiscrete vK.v] [CompleteSpace K]

@[simp]
theorem restrictNormal_eq_self {F E : Type*}  [Field F] [Field E] [Algebra F E] [Algebra F E] (s : E ≃ₐ[F] E) [Normal F E] : s.restrictNormal E = s := by
  ext x
  calc
  _ = (algebraMap E E) ((s.restrictNormal E) x) := by simp
  _ = _ := by
    rw [AlgEquiv.restrictNormal_commutes]
    simp

theorem restrictNormal_restrictNormal {F K₁ K₂ : Type*} [Field F] [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂]  (s : K₁ ≃ₐ[F] K₂) (E M: Type*) [Field E] [Field M] [Algebra F M] [Algebra F E] [Algebra M E] [Algebra M K₁] [Algebra M K₂] [Algebra E K₁] [Algebra E K₂] [IsScalarTower F M K₁] [IsScalarTower F M K₂] [IsScalarTower F E K₁] [IsScalarTower F E K₂]  [Normal F E] [Normal F M] [IsScalarTower F M E] : (s.restrictNormal E).restrictNormal M = s.restrictNormal M := by sorry


-- theorem relation with aux
theorem eq_UpperRamificationGroup_aux [vL : Valued L ℤₘ₀] [IsDiscrete vL.v] [IsValExtension K L] [FiniteDimensional K L] [Normal K L] {v : ℚ} : upperRamificationGroup K L v = upperRamificationGroup_aux K L v := by
  ext s
  simp only [upperRamificationGroup, Subgroup.mem_mk, Set.mem_setOf_eq]
  constructor
  · intro h
    have hL := h L
    suffices restrictNormalHom (F := K) L = MonoidHom.id _ by
      simp [this] at hL
      assumption
    ext s a
    simp [restrictNormalHom]
  · sorry
  -- · intro h F
  --   intros
  --   rw [← herbrand' (L := L)]
  --   apply Subgroup.mem_map_of_mem
  --   exact h

-- universe problem here. `∀ (F : Type u_2)`
theorem mem_iff_mem_UpperRamificationGroup_aux {s : L ≃ₐ[K] L} {v : ℚ} : s ∈ G(L/K)^[v] ↔ ∀ (F : Type u_2) [Field F] [vF : Valued F ℤₘ₀] [IsDiscrete vF.v] [Algebra K F] [IsValExtension K F] [Algebra F L] [IsScalarTower K F L] [Normal K F] [FiniteDimensional K F],
    restrictNormalHom F s ∈ upperRamificationGroup_aux K F v := by
  rfl

-- theorem upperRamificationGroup_eq_iInf {v : ℚ} : G(L/K)^[v] =
--   iInf fun (⟨F,hF⟩ : {F : IntermediateField K L // Normal K F ∧ FiniteDimensional K F}) =>
--     haveI := hF.1
--     haveI := hF.2
--     (upperRamificationGroup_aux K F v).comap (restrictNormalHom (E := F))
--     := by
--   ext s
--   simp only
--   rw [mem_iff_mem_UpperRamificationGroup_aux, Subgroup.mem_iInf]
--   simp only [Subgroup.mem_comap, Subtype.forall]
--   constructor <;> intro h F
--   · intro hF
--     exact @h F hF.1 hF.2
--   · intro h1 h2
--     exact h F ⟨h1,h2⟩


-- theorem compatible with quotient, finite quotient
@[simp]
theorem map_restrictNormalHom {K'} [Field K'] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L] [Normal K K'] [Normal K L] (v : ℚ) : G(L/K)^[v].map (AlgEquiv.restrictNormalHom K') = G(K'/K)^[v] := by
  sorry
  /-
  ext s
  calc
  _ ↔ ∀ (F : IntermediateField K L) [Normal K F] [FiniteDimensional K F],
      s ∈ ((upperRamificationGroup_aux K F v).comap (restrictNormalHom (K₁ := L) F)).map (restrictNormalHom K') := by
    simp [mem_iff_mem_UpperRamificationGroup_aux]
    sorry
  _ ↔ ∀ (F : IntermediateField K L) [Normal K F] [FiniteDimensional K F],
      letI : FiniteDimensional K (F.comap (IsScalarTower.toAlgHom K K' L)) := sorry
      letI : Normal K (F.comap (IsScalarTower.toAlgHom K K' L)) := sorry
      s ∈ (upperRamificationGroup_aux K (F.comap (IsScalarTower.toAlgHom K K' L)) v).comap (restrictNormalHom (K₁ := K') (F.comap (IsScalarTower.toAlgHom K K' L))) := by
        constructor <;> intro h F _ _
        simp at h ⊢
        sorry
        sorry
  _ ↔ ∀ (F : IntermediateField K K') [Normal K F] [FiniteDimensional K F],
      s ∈ (upperRamificationGroup_aux K F v).comap (restrictNormalHom (K₁ := K') F) := sorry
  _ ↔ _ := by exact mem_iff_mem_UpperRamificationGroup_aux
  -/
  -- ext s
  -- -- simp [upperRamificationGroup]
  -- constructor <;> intro h
  -- · simp only [Subgroup.mem_map] at h
  --   obtain ⟨t, ⟨ht, rfl⟩⟩ := h
  --   rw [mem_iff_mem_UpperRamificationGroup_aux] at ht ⊢
  --   intro F _ _
  --   have : ∀ x : K', (IsScalarTower.toAlgHom K K' L) x ∈ (IntermediateField.map (IsScalarTower.toAlgHom K K' L) F) ↔ x ∈ F := sorry
  --   haveI : Normal K (IntermediateField.map (IsScalarTower.toAlgHom K K' L) F) := sorry
  --   haveI : FiniteDimensional K (IntermediateField.map (IsScalarTower.toAlgHom K K' L) F) := sorry
  --   have := ht (F.map (IsScalarTower.toAlgHom K K' L) : IntermediateField K L)
  --   simp only [toSubalgebra_map] at this
  --   sorry
  --   -- rw [IntermediateField.coe_map] at this
  -- ·

theorem mem_iff {s : L ≃ₐ[K] L} {v : ℚ} : s ∈ G(L/K)^[v] ↔ ∀ (F : IntermediateField K L) [Normal K F] [FiniteDimensional K F],
      s.restrictNormal F ∈ G(F/K)^[v] := by
  conv =>
    rhs
    intro F i i'
    rhs
    -- rw [eq_UpperRamificationGroup_aux (K := K) (L := F)]
  sorry

section autCongr

variable {L': Type*} [Field L'] [Algebra K L']

theorem autCongr_mem_upperRamificationGroup_iff {f : L ≃ₐ[K] L'} (s : L ≃ₐ[K] L) (v : ℚ) : s ∈ G(L/K)^[v] ↔ (AlgEquiv.autCongr f s : L' ≃ₐ[K] L') ∈ G(L'/K)^[v] := by
  sorry

end autCongr

-- theorems about exhausive and separated
-- under what condition this is correct? this is too strong?
theorem eq_decompositionGroup [vL : Valued L ℤₘ₀] [IsDiscrete vL.v] [IsValExtension K L] [FiniteDimensional K L] [Normal K L] {v : ℚ} (h : v ≤ -1) :
G(L/K)^[v] = decompositionGroup K L := by
  rw [eq_UpperRamificationGroup_aux]
  exact UpperRamificationGroup_aux.eq_decompositionGroup h

theorem eq_top [vL : Valued L ℤₘ₀] [IsDiscrete vL.v] [IsValExtension K L] [FiniteDimensional K L] [Normal K L] {v : ℚ} (h : v ≤ -1) : G(L/K)^[v] = ⊤ := by
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
