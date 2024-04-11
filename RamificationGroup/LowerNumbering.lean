import RamificationGroup.Valued.Hom.ValExtension
import RamificationGroup.ForMathlib.Algebra.Algebra.Tower
import Mathlib.FieldTheory.Galois
import LocalClassFieldTheory.LocalField

/-
# Lower Numbering Ramification Group

## Main Definitions

## Main Theorem

## TODO

prove theorems using Bichang's preparation in section SeparatedExhausive

rename theorems, many theorem should be named as LowerRamificationGroup.xxx, not lowerRamificationGroup_xxx

-/

open DiscreteValuation Valued Valuation

section DecompositionGroup

variable (R S : Type*) {ΓS : outParam Type*} [CommRing R] [Ring S]
[LinearOrderedCommGroupWithZero ΓS] [vS : Valued S ΓS] [Algebra R S]

variable {S} in
theorem Valuation.IsEquiv_comap_symm {s : S ≃+* S} (h : vS.v.IsEquiv (vS.v.comap s)) : vS.v.IsEquiv (vS.v.comap s.symm) := by
  intro x y
  convert (h (s.symm x) (s.symm y)).symm using 2 <;>
  simp

namespace Valued

def decompositionGroup : Subgroup (S ≃ₐ[R] S) where
  carrier := {s | vS.v.IsEquiv <| vS.v.comap s}
  mul_mem' {s} {s'} hs hs' x y := by
    calc
      _ ↔ (vS.v.comap s' x) ≤ (vS.v.comap s') y := hs' x y
      _ ↔ _ := hs _ _
  one_mem' := by
    apply Valuation.IsEquiv.refl
  inv_mem' {_} {h} := by
    apply Valuation.IsEquiv_comap_symm
    exact h

end Valued

end DecompositionGroup

-- <-1 decomposition group
-- >= -1 decompositiongroup and v (s x - x) ≤ 1
section

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vS : Valued S ℤₘ₀] [Algebra R S]

-- variable (K L : Type*) {ΓL : outParam Type*} [Field K] [Field L] [LinearOrderedCommGroupWithZero ΓL] [vL : Valued L ℤₘ₀] [Algebra K L]

def lowerRamificationGroup (i : ℤ) : Subgroup (S ≃ₐ[R] S) where
    carrier := {s | s ∈ decompositionGroup R S ∧ ∀ x : vS.v.integer, Valued.v (s x - x) ≤ .coe (.ofAdd (- i - 1))}
    mul_mem' {a} {b} ha hb := by
      constructor
      · exact mul_mem ha.1 hb.1
      · intro x
        calc
          _ = v (a (b x) - x) := rfl
          _ = v ((a (b x) - b x) + (b x - x)) := by congr; simp
          _ ≤ max (v (a (b x) - b x)) (v (b x - x)) := Valuation.map_add _ _ _
          _ ≤ max (.coe (.ofAdd (- i - 1))) (.coe (.ofAdd (- i - 1))) := by
            apply max_le_max
            · exact ha.2 ⟨b x, (val_map_le_one_iff hb.1 x).mpr x.2⟩
            · exact hb.2 x
          _ = _ := max_self _
    one_mem' := by
      constructor
      · exact one_mem _
      · simp
    inv_mem' {s} hs := by
      constructor
      · exact inv_mem hs.1
      intro a
      calc
      _ = v (s⁻¹ a - a) := rfl
      _ = v ( s⁻¹ a - s (s⁻¹ a) ) := by
        congr 1
        simp only [sub_right_inj]
        exact (EquivLike.apply_inv_apply s ↑a).symm
      _ = v ( s (s⁻¹ a) - s ⁻¹ a) := by
        rw [← Valuation.map_neg]
        congr
        simp
      _ ≤ _ := hs.2 ⟨s⁻¹ a, (val_map_le_one_iff (f := (s.symm : S →+* S))
        (Valuation.IsEquiv_comap_symm hs.1) a.1).mpr a.2⟩

scoped [Valued] notation:max " G(" S:max "/" R:max ")_[" n:max "] " => lowerRamificationGroup R S n

theorem lowerRamificationGroup.antitone : Antitone (lowerRamificationGroup R S) := by
  rintro a b hab
  simp only [lowerRamificationGroup, ofAdd_sub, ofAdd_neg, Subtype.forall, Subgroup.mk_le_mk,
    Set.setOf_subset_setOf, and_imp]
  rintro s hs1 hs2
  constructor
  · exact hs1
  · intro y hy
    apply le_trans
    apply hs2 y hy
    simp only [WithZero.coe_le_coe, div_le_iff_le_mul, div_mul_cancel', inv_le_inv_iff,
      Multiplicative.ofAdd_le]
    exact hab

end


section WithBot
-- this should be put into a suitable place, Also add `WithOne`? `WithTop`, `WithBot`, `WithOne`, `Muliplicative`, `Additive`
open Classical

-- there is no `ConditionallyCompleteLinearOrderTop` in mathlib ...
#check WithBot.linearOrder
noncomputable instance {α} [ConditionallyCompleteLinearOrder α] : ConditionallyCompleteLinearOrderBot (WithBot α) where
  toConditionallyCompleteLattice := WithBot.conditionallyCompleteLattice
  le_total := WithBot.linearOrder.le_total
  decidableLE := WithBot.decidableLE
  decidableEq := WithBot.decidableEq
  decidableLT := WithBot.decidableLT
  csSup_of_not_bddAbove s h := by
    by_cases hbot : s ⊆ {⊥}
    · simp [sSup, sInf]
      sorry
    · simp [sSup, sInf]
      intro x hxs hx
      sorry
  csInf_of_not_bddBelow := sorry
  bot_le := WithBot.orderBot.bot_le
  csSup_empty := by simp only [WithBot.csSup_empty]

noncomputable instance {α} [ConditionallyCompleteLinearOrder α] : ConditionallyCompleteLinearOrderBot (WithZero α) := inferInstanceAs (ConditionallyCompleteLinearOrderBot (WithBot α))

instance {α} [Add α] [ConditionallyCompleteLinearOrder α] : ConditionallyCompleteLinearOrder (Multiplicative α) := inferInstanceAs (ConditionallyCompleteLinearOrder α)

-- instance : ConditionallyCompleteLinearOrderBot ℤₘ₀ := inferInstanceAs (ConditionallyCompleteLinearOrderBot (WithZero ℤ))

end WithBot

section lowerIndex

variable (R S : Type*) [CommRing R] [Ring S] [vS : Valued S ℤₘ₀] [Algebra R S]

open Classical
-- 0 if lower than 0
noncomputable def AlgEquiv.lowerIndex (s : S ≃ₐ[R] S) : ℕ∞ :=
  if h : iSup (fun x : vS.v.integer => (Valued.v (s x - x))) = 0 then ⊤
  else (- Multiplicative.toAdd (WithZero.unzero h)).toNat

scoped [Valued] notation:max " i_[" S:max "/" R:max "]" => AlgEquiv.lowerIndex R S

noncomputable def AlgEquiv.truncatedLowerIndex (u : ℚ) (s : (S ≃ₐ[R] S)) : ℚ :=
  if h : i_[S/R] s = ⊤ then u
  else min u ((i_[S/R] s).untop h)

scoped [Valued] notation:max " i_[" L:max "/" K:max "]ₜ" => AlgEquiv.truncatedLowerIndex K L

#check AlgEquiv.truncatedLowerIndex

end lowerIndex

variable {R : Type*} {R' S: Type*} {ΓR ΓS ΓA ΓB : outParam Type*} [CommRing R] [CommRing R'] [Ring S]
[vS : Valued S ℤₘ₀]
[Algebra R S] [Algebra R R'] [Algebra R' S] [IsScalarTower R R' S]

@[simp]
theorem lowerIndex_refl : (i_[S/R] .refl) = ⊤ := by
  simp [AlgEquiv.lowerIndex]

@[simp]
theorem truncatedLowerIndex_refl (u : ℚ) : AlgEquiv.truncatedLowerIndex R S u .refl = u := by
  simp [AlgEquiv.truncatedLowerIndex]

section

variable {K K' L : Type*} {ΓK ΓK' : outParam Type*} [CommRing K] [Field K'] [Field L] [LinearOrderedCommGroupWithZero ΓK]
[LinearOrderedCommGroupWithZero ΓK'] [vL : Valued L ℤₘ₀] [Algebra K L]
[Algebra K K'] [Algebra K' L] [IsScalarTower K K' L]

@[simp]
theorem lowerIndex_eq_top_iff_eq_refl {s : L ≃ₐ[K] L} : i_[L/K] s = ⊤ ↔ s = .refl := by
  constructor <;>
  intro h
  · ext l
    simp only [AlgEquiv.coe_refl, id_eq]
    obtain ⟨x, ⟨y, ⟨_, rfl⟩⟩⟩ := IsFractionRing.div_surjective l (A := 𝒪[L])
    simp
    by_cases hs : iSup (fun x : vL.v.integer => (v (s x - x))) = 0
    · simp only [AddSubgroupClass.coe_sub] at hs
      have : ∀ x : vL.v.integer, v (s x - x) = 0 := by
        intro x
        apply le_of_eq at hs
        rw [show (0 : ℤₘ₀) = ⊥ by rfl, eq_bot_iff]
        exact (ciSup_le_iff' sorry).mp hs x -- this sorry is should be filled with bounded by one
      sorry
    · simp only [AlgEquiv.lowerIndex, AddSubgroupClass.coe_sub,
      dite_eq_left_iff, ENat.coe_ne_top, imp_false, not_not] at h
      have h : ∀ x : 𝒪[L], v (s ↑x - ↑x) = 0 := sorry
      --exact h l
      sorry
  · simp [AlgEquiv.lowerIndex, h]

--the type of n should be changed
-- instead, change when use this theorem
theorem mem_lowerRamificationGroup_iff {s : L ≃ₐ[K] L} (n : ℕ) : s ∈ G(L/K)_[n] ↔ (n + 1 : ℕ) ≤ i_[L/K] s := by
  simp [AlgEquiv.truncatedLowerIndex]
  constructor <;>
  unfold lowerRamificationGroup AlgEquiv.lowerIndex
  simp
  rintro h
  by_cases hs : iSup (fun x : vL.v.integer => (v (s x - x))) = 0
  · simp at hs
    simp [hs]
  · simp at hs
    simp [hs]
    sorry
  simp
  sorry


theorem mem_lowerRamificationGroup_of_le_truncatedLowerIndex_sub_one {s : L ≃ₐ[K] L} {u r : ℚ} (h : u ≤ i_[L/K]ₜ r s - 1) : s ∈ G(L/K)_[⌈u⌉] := by
  unfold AlgEquiv.truncatedLowerIndex at h
  by_cases hs : i_[L/K] s = ⊤
  · simp [hs] at h
    --maybe there is a better way
    have : (⌈u⌉.toNat + 1) ≤ i_[L/K] s := by simp [hs]
    convert (mem_lowerRamificationGroup_iff ⌈u⌉.toNat).2 this
    sorry
  · simp [hs] at h
    have : (⌈u⌉.toNat + 1) ≤ i_[L/K] s := by
      have h' : u + 1 ≤ min r ↑(WithTop.untop (i_[L/K] s) hs) := by linarith [h]
      have hnt: i_[L/K] s = (WithTop.untop (i_[L/K] s) hs) := by sorry
      rw [hnt]
      convert (le_min_iff.1 h').right
      sorry
    convert (mem_lowerRamificationGroup_iff ⌈u⌉.toNat).2 this
    sorry

theorem le_truncatedLowerIndex_sub_one_iff_mem_lowerRamificationGroup (s : L ≃ₐ[K] L) (u : ℚ) (r : ℚ) (h : u + 1 ≤ r) : u ≤ i_[L/K]ₜ r s - 1 ↔ s ∈ G(L/K)_[⌈u⌉] := by
  constructor
  apply mem_lowerRamificationGroup_of_le_truncatedLowerIndex_sub_one
  rintro hs
  unfold AlgEquiv.truncatedLowerIndex
  by_cases hc : i_[L/K] s = ⊤
  · simp [hc]
    linarith [h]
  · have : ⌈u⌉.toNat + 1 ≤ i_[L/K] s := by
      sorry
      --apply (mem_lowerRamificationGroup_iff ⌈u⌉.toNat).1 hs
    simp [hc]
    sorry

end

@[simp]
theorem lowerIndex_restrictScalars (s : S ≃ₐ[R'] S) : i_[S/R] (s.restrictScalars R) =  i_[S/R'] s := rfl

@[simp]
theorem truncatedLowerIndex_restrictScalars (u : ℚ) (s : S ≃ₐ[R'] S) : i_[S/R]ₜ u (s.restrictScalars R) = i_[S/R']ₜ u s := rfl

@[simp]
theorem lowerRamificationGroup_restrictScalars (u : ℤ) : G(S/R)_[u].comap (AlgEquiv.restrictScalarsHom R) = G(S/R')_[u] := rfl


section ExhausiveSeperated

variable {R : Type*} {R' S: Type*} {ΓR ΓS ΓA ΓB : outParam Type*} [CommRing R] [CommRing R'] [Ring S]
[vS : Valued S ℤₘ₀] [Algebra R S] [Algebra R R'] [Algebra R' S] [IsScalarTower R R' S]

theorem lowerRamificationGroup_eq_decompositionGroup {u : ℤ} (h : u ≤ -1) :
G(S/R)_[u] = decompositionGroup R S := by
  ext s
  simp only [lowerRamificationGroup, ofAdd_sub, ofAdd_neg, Subtype.forall, Subgroup.mem_mk,
    Set.mem_setOf_eq, and_iff_left_iff_imp]
  intro hs a ha
  calc
    _ ≤ max (v (s a)) (v a) := Valuation.map_sub _ _ _
    _ ≤ 1 := by
      apply max_le
      · exact (val_map_le_one_iff hs a).mpr ha
      · exact ha
    _ ≤ _ := by
      show (.coe (0 : ℤ) : ℤₘ₀) ≤ .coe ((- u - 1) : ℤ)
      norm_cast
      show (0 : ℤ) ≤ - u - 1
      linarith

section

variable {K L : Type*} [Field K] [Field L] [vK : Valued K ℤₘ₀] [vL : Valued L ℤₘ₀] [Algebra K L]

-- this completeness implies unique extension of valuation, need to use Bichang's work
@[simp]
theorem decompositionGroup_eq_top [IsValExtension K L] [CompleteSpace K] : decompositionGroup K L = ⊤ := sorry

theorem lowerRamificationGroup_eq_top [IsValExtension K L] [CompleteSpace K] {u : ℤ} (h : u ≤ -1) : G(L/K)_[u] = ⊤ := by
  rw [lowerRamificationGroup_eq_decompositionGroup h, decompositionGroup_eq_top]

end

section

variable {K L : Type*} [Field K] [Field L] [vK : Valued K ℤₘ₀]  [vL : Valued L ℤₘ₀]

-- this uses local fields and bichang's work, check if the condition is too strong..., It should be O_L is finitely generated over O_K
theorem exist_lowerRamificationGroup_eq_bot [LocalField K] [LocalField L] [Algebra K L] : ∃ u : ℤ, G(L/K)_[u] = ⊥ := sorry

end

end ExhausiveSeperated
