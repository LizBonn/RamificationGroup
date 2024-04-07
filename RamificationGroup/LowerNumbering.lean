import RamificationGroup.Valued.Hom.ValExtension
import RamificationGroup.ForMathlib.Algebra.Algebra.Tower
import Mathlib.FieldTheory.Galois

open DiscreteValuation Valued Valuation

/-
section preparation

namespace RingHom

variable {R : Type*} {ΓR : outParam Type*} [Ring R] [LinearOrderedCommGroupWithZero ΓR] {v : Valuation R ΓR}

def liftValuationInteger {f : R →+* R} (hf : ∀ x : v.integer, v (f x - x) ≤ 1) : v.integer →+* v.integer where
  toFun r := {
    val := f r
    property := by
      calc
        v (f r) = v (f r - r + r) := by
          congr
          simp
        _ ≤ max (v (f r - r)) (v (r : R)) := Valuation.map_add _ _ _
        _ ≤ 1 := max_le (hf r) r.2
  }
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp
  map_zero' := by
    ext
    simp
  map_add' _ _ := by
    ext
    simp

end RingHom

variable {R : Type*} {ΓR : outParam Type*} [Ring R] [LinearOrderedCommGroupWithZero ΓR] (v : Valuation R ΓR)

variable {K : Type*} {ΓK : outParam Type*} [Field K] [LinearOrderedCommGroupWithZero ΓK] [vK : Valued K ΓK]

theorem Valuation.integer.val_symm_sub_le_one {s : R ≃+* R} (hs : ∀ x : v.integer, v (s x - x) ≤ 1) (r : v.integer): v (s.symm r - r) ≤ 1 := by
  calc
    _ = v (s (s.symm r) - s.symm r) := by
      rw [← Valuation.map_neg]
      congr 1
      simp
    _ ≤ 1 := hs (s.symm r)

namespace RingEquiv

-- 1 = .coe (.ofAdd 0)
def liftValuationInteger {s : R ≃+* R} (hs : ∀ x : v.integer, v (s x - x) ≤ 1) : v.integer ≃+* v.integer := {
  s.toRingHom.liftValuationInteger hs with
  invFun := _
  left_inv := _
  right_inv := _
}
  -- {
  --   (s : R →+* R).liftValuationInteger with
  --   invFun := sorry
  -- }

def liftValuedValuationSubring {s : K ≃+* K} (hs : ∀ x : vK.v.integer, Valued.v (s x - x) ≤ 1) : 𝒪[K] ≃+* 𝒪[K] := sorry

end RingEquiv

end preparation
-/

section DecompositionGroup

variable (R S : Type*) {ΓS : outParam Type*} [CommRing R] [Ring S]
[LinearOrderedCommGroupWithZero ΓS] [vS : Valued S ΓS] [Algebra R S]

variable {S} in
theorem Valuation.IsEquiv_comap_symm {s : S ≃+* S} (h : vS.v.IsEquiv (vS.v.comap s)) : vS.v.IsEquiv (vS.v.comap s.symm) := by
  intro x y
  convert (h (s.symm x) (s.symm y)).symm using 2 <;>
  simp

def Valued.decompositionGroup : Subgroup (S ≃ₐ[R] S) where
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


-- -- Is such a bundled version better? OrderDual can be add at either source or target.
-- def lowerRamificationGroup' : OrderHom ℤᵒᵈ (Subgroup (S ≃ₐv[R] S)) where
--   toFun i := {
--     carrier := {s | ∀ x : vS.v.integer, vS.v (s x - x) ≤ .coe (.ofAdd (- OrderDual.ofDual i - 1)) }
--     mul_mem' := sorry
--     one_mem' := sorry
--     inv_mem' := sorry
--   }
--   monotone' := sorry

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

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vS : Valued S ℤₘ₀] [Algebra R S]

open Classical
-- 0 if lower than 0
noncomputable def AlgEquiv.lowerIndex (s : S ≃ₐ[R] S) : ℕ∞ :=
  if h : iSup (fun x : vS.v.integer => (Valued.v (s x - x))) = 0 then ⊤
  else (- Multiplicative.toAdd (WithZero.unzero h)).toNat

scoped [Valued] notation:max " G(" S:max "/" R:max ")_[" n:max "] " => lowerRamificationGroup R S n

scoped [Valued] notation:max " i_[" S:max "/" R:max "]" => AlgEquiv.lowerIndex R S

noncomputable def ValAlgEquiv.truncatedLowerIndex (u : ℚ) (s : (S ≃ₐ[R] S)) : ℚ :=
  if h : i_[S/R] s = ⊤ then u
  else min u ((i_[S/R] s).untop h)

scoped [Valued] notation:max " i_[" L:max "/" K:max "]ₜ" => ValAlgEquiv.truncatedLowerIndex K L

#check ValAlgEquiv.truncatedLowerIndex

end lowerIndex

#check AlgEquiv.restrictScalars

variable {K K' L : Type*} {ΓK ΓK' : outParam Type*} [Field K] [Field K'] [Field L] [LinearOrderedCommGroupWithZero ΓK]
[LinearOrderedCommGroupWithZero ΓK']
[vK : Valued K ΓK] [vK' : Valued K' ΓK'] [vL : Valued L ℤₘ₀] [Algebra K L] --{H : Subgroup (L ≃ₐ[K] L)} [H.Normal]
[Algebra K K'] [Algebra K' L] [IsScalarTower K K' L]

section

variable (R : Type*) {S A B : Type*} {ΓR ΓS ΓA ΓB : outParam Type*} [CommRing R] [CommRing S] [Ring A] [Ring B]
[LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS]
[LinearOrderedCommGroupWithZero ΓA]
[LinearOrderedCommGroupWithZero ΓB]
[vR : Valued R ΓR] [vS : Valued S ΓS] [vA : Valued A ΓA] [vB : Valued B ΓB]
[Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [Algebra S B] [IsScalarTower R S A] [IsScalarTower R S B]

#synth CommSemiring R

#check AlgEquiv.restrictScalars

end

@[simp]
theorem lowerIndex_refl : (i_[L/K] .refl) = ⊤ := by
  simp [AlgEquiv.lowerIndex]

@[simp]
theorem truncatedLowerIndex_refl (u : ℚ) : ValAlgEquiv.truncatedLowerIndex K L u .refl = u := by
  simp [ValAlgEquiv.truncatedLowerIndex]
/-
noncomputable def ValAlgEquiv.lowerIndex (s : S ≃ₐv[R] S) : ℕ∞ :=
  if h : iSup (fun x : vS.v.integer => (Valued.v (s.liftInteger x - x))) = 0 then ⊤
  else (- Multiplicative.toAdd (WithZero.unzero h)).toNat
-/

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
theorem mem_lowerRamificationGroup_iff {s : L ≃ₐ[K] L} (n : ℕ) : s ∈ G(L/K)_[n] ↔ (n + 1 : ℕ) ≤ i_[L/K] s := by
  simp [ValAlgEquiv.truncatedLowerIndex]
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
  unfold ValAlgEquiv.truncatedLowerIndex at h
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
  unfold ValAlgEquiv.truncatedLowerIndex
  by_cases hc : i_[L/K] s = ⊤
  · simp [hc]
    linarith [h]
  · have : ⌈u⌉.toNat + 1 ≤ i_[L/K] s := by
      sorry
      --apply (mem_lowerRamificationGroup_iff ⌈u⌉.toNat).1 hs
    simp [hc]
    sorry


@[simp]
theorem lowerIndex_restrictScalars (s : L ≃ₐ[K'] L) : i_[L/K] (s.restrictScalars K) =  i_[L/K'] s := rfl

@[simp]
theorem truncatedLowerIndex_restrictScalars (u : ℚ) (s : L ≃ₐ[K'] L) : i_[L/K]ₜ u (s.restrictScalars K) = i_[L/K']ₜ u s := rfl

@[simp]
theorem lowerRamificationGroup_restrictScalars (u : ℤ) : G(L/K)_[u].comap (AlgEquiv.restrictScalarsHom K) = G(L/K')_[u] := rfl
