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

variable {K K' L : Type*} {ΓK : outParam Type*} [Field K] [Field K'] [Field L] [vK' : Valued K' ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK'.v] [IsDiscrete vL.v] [Algebra K L] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L] [IsValExtension K' L] [Normal K K'] [Normal K L] [FiniteDimensional K L] [FiniteDimensional K K']

variable (σ : K' ≃ₐ[K] K')

open Classical
-- Lemma 4
theorem preimage_singleton_nonempty {σ : K' ≃ₐ[K] K'} : ((AlgEquiv.restrictNormalHom K' (K₁ := L))⁻¹' {σ}).toFinset.Nonempty := by
  apply Finset.coe_nonempty.mp
  simp only [Set.coe_toFinset]
  exact Set.Nonempty.preimage (Set.singleton_nonempty _) (AlgEquiv.restrictNormalHom_surjective (F := K) (E := L) (K₁ := K'))

variable (L) in
def HerbrandFunction.truncatedJ (u : ℚ) (σ : K' ≃ₐ[K] K') : ℚ := Finset.max' (((AlgEquiv.restrictNormalHom K')⁻¹' {σ}).toFinset.image (fun (x : L ≃ₐ[K] L) => x.truncatedLowerIndex K L u - 1)) (Finset.Nonempty.image preimage_singleton_nonempty _)


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

#check AlgEquiv

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
        ext k
        simp
        sorry⟩
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
  sorry

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

-- Lemma 5
@[simp]
theorem herbrand (u : ℚ) : G(L/K)_[⌈u⌉].map (AlgEquiv.restrictNormalHom K') = G(K'/K)_[⌈phi K' L u⌉] := by
  ext σ
  calc
  _ ↔ truncatedJ L (u + 1) σ - 1 ≥ u :=
  (le_truncatedJ_sub_one_iff_mem_lowerRamificationGroup (by linarith)).symm
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

instance valuedIntermediateField : Valued K' ℤₘ₀ := DiscreteValuation.Extension.valued K K'

/- -- success
#synth IsDiscrete (valuedIntermediateField.v : Valuation K' _)
-/

-- this is needed, or #synth CompleteSpace K' fails
-- `when is this needed?`
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

open AlgEquiv
-- this is easier to use
def upperRamificationGroup (K L : Type*) [Field K] [vK : Valued K ℤₘ₀] [Field L] [Algebra K L] [IsDiscrete vK.v] [CompleteSpace K] (v : ℚ) : Subgroup (L ≃ₐ[K] L) where
  carrier := {s | ∀ (F : IntermediateField K L) [Normal K F] [FiniteDimensional K F],
    restrictNormalHom F s ∈ upperRamificationGroup_aux K F v}
  mul_mem' {s} {s'} hs hs' F _ _ := by
    rw [(restrictNormalHom F).map_mul s s']
    exact Subgroup.mul_mem (upperRamificationGroup_aux K F v) (hs F) (hs' F)
  one_mem' F _ _ := by
    rw [(restrictNormalHom F).map_one]
    exact Subgroup.one_mem (upperRamificationGroup_aux K F v)
  inv_mem' {s} hs F _ _ := by
    rw [(restrictNormalHom F).map_inv s]
    exact Subgroup.inv_mem (upperRamificationGroup_aux K F v) (hs F)

#check upperRamificationGroup

scoped [Valued] notation:max " G(" L:max "/" K:max ")^[" v:max "] " => upperRamificationGroup K L v

namespace UpperRamificationGroup

variable {K L : Type*} [Field K] [vK : Valued K ℤₘ₀] [Field L] [Algebra K L] [IsDiscrete vK.v] [CompleteSpace K]

-- theorem relation with aux
theorem eq_UpperRamificationGroup_aux [vL : Valued L ℤₘ₀] [IsDiscrete vL.v] [IsValExtension K L] [FiniteDimensional K L] [Normal K L] {v : ℚ} : upperRamificationGroup K L v = upperRamificationGroup_aux K L v := by
  ext s
  simp only [upperRamificationGroup, Subgroup.mem_mk, Set.mem_setOf_eq]
  constructor
  · intro h
    haveI := Normal.of_algEquiv (F := K) (E := L) (IntermediateField.topEquiv.symm)
    have htop := h ⊤
    sorry -- `should use equiv of valuation on Top or L`
    -- exact h (⊤ : IntermediateField K L) -- Add theorems of isom
  · intro h F _ _
    rw [← herbrand' (L := L)]
    apply Subgroup.mem_map_of_mem
    exact h

theorem mem_iff_mem_UpperRamificationGroup_aux {s : L ≃ₐ[K] L} {v : ℚ} : s ∈ G(L/K)^[v] ↔ ∀ (F : IntermediateField K L) [Normal K F] [FiniteDimensional K F],
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
    rw [(eq_UpperRamificationGroup_aux (K := K) (L := F))]

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
