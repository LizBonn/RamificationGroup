import RamificationGroup.Valued.Hom.Lift
import RamificationGroup.ForMathlib.Algebra.Algebra.Tower
import LocalClassFieldTheory.LocalField.Basic
import RamificationGroup.ForMathlib.Algebra.Algebra.PowerBasis
import RamificationGroup.Valued.AlgebraicInstances
import RamificationGroup.Valuation.Extension
import RamificationGroup.Valued.Hom.ValExtension
import RamificationGroup.Valued.AlgebraicInstances
/-
# Lower Numbering Ramification Group

## Main Definitions

## Main Theorem

## TODO

prove theorems using Bichang's preparation in section SeparatedExhausive

rename theorems, many theorem should be named as LowerRamificationGroup.xxx, not lowerRamificationGroup_xxx

-/

open DiscreteValuation Valued Valuation

section general_algebra

instance instAlgebraFiniteTypeToIsNoetherian (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [IsNoetherian R A] :
  Algebra.FiniteType R A where
    out := by
      apply Subalgebra.fg_of_fg_toSubmodule
      rw [Algebra.top_toSubmodule]
      apply isNoetherian_def.mp
      assumption

end general_algebra

-- <-1 decomposition group
-- >= -1 decompositiongroup and v (s x - x) ≤ 1
section def_lower_rami_grp

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [vS : Valued S ℤₘ₀] [Algebra R S]

def lowerRamificationGroup (u : ℤ) : Subgroup (S ≃ₐ[R] S) where
    carrier := {s | s ∈ decompositionGroup R S ∧ ∀ x : vS.v.integer, Valued.v (s x - x) ≤ .coe (.ofAdd (- u - 1))}
    mul_mem' {a} {b} ha hb := by
      constructor
      · exact mul_mem ha.1 hb.1
      · intro x
        calc
          _ = v (a (b x) - x) := rfl
          _ = v ((a (b x) - b x) + (b x - x)) := by congr; simp
          _ ≤ max (v (a (b x) - b x)) (v (b x - x)) := Valuation.map_add _ _ _
          _ ≤ max (.coe (.ofAdd (- u - 1))) (.coe (.ofAdd (- u - 1))) := by
            apply max_le_max
            · exact ha.2 ⟨b x, (val_map_le_one_iff hb.1 x).mpr x.2⟩
            · exact hb.2 x
          _ = _ := max_self _
    one_mem' := by
      constructor
      · exact one_mem _
      · simp only [AlgEquiv.one_apply, sub_self, _root_.map_zero, ofAdd_sub, ofAdd_neg, zero_le',
        Subtype.forall, implies_true, forall_const]
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
        simp only [neg_sub]
      _ ≤ _ := hs.2 ⟨s⁻¹ a, (val_map_le_one_iff (f := (s.symm : S →+* S))
        (Valuation.IsEquiv_comap_symm hs.1) a.1).mpr a.2⟩

scoped [Valued] notation:max " G(" S:max "/" R:max ")_[" u:max "] " => lowerRamificationGroup R S u

theorem lowerRamificationGroup.antitone : Antitone (lowerRamificationGroup R S) := by
  intro a b hab
  simp only [lowerRamificationGroup, ofAdd_sub, ofAdd_neg, Subtype.forall, Subgroup.mk_le_mk,
    Set.setOf_subset_setOf, and_imp]
  rintro s hs1 hs2
  constructor
  · exact hs1
  · intro y hy
    apply le_trans (hs2 y hy)
    simp only [WithZero.coe_le_coe, div_le_iff_le_mul, div_mul_cancel, inv_le_inv_iff,
      Multiplicative.ofAdd_le]
    exact hab

end def_lower_rami_grp

instance Valuation.instNonemptyToValuation {R Γ₀: Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀): Nonempty v.integer := Zero.instNonempty

section autCongr

variable {R S S': Type*} {ΓR : outParam Type*} [CommRing R] [Ring S] [Ring S'] [vS : Valued S ℤₘ₀] [vS : Valued S' ℤₘ₀] [Algebra R S] [Algebra R S']

#check comap
--if f is a R-algebra isom of S and S', f preserves the valuation, then s ∈ G(S/R)_[u] if and only if F s ∈ G(S'/R)_[u], where F : Gal(S/R) → Gal(S'/R), F(σ)(s') = σ(f⁻¹(s')).
--the u-th lower ramification groups of two isomorphic ring extensions are isomorphic for all u ∈ ℤ.
theorem autCongr_mem_lowerRamificationGroup_iff {f : S ≃ₐ[R] S'} (hf : ∀ a : S, v a = v (f a)) (s : S ≃ₐ[R] S) (u : ℤ) : s ∈ G(S/R)_[u] ↔ (AlgEquiv.autCongr f s : S' ≃ₐ[R] S') ∈ G(S'/R)_[u] := by
  have hf' : ∀ a : S', v (f.symm a) = v a := by
    intro a
    rw [hf (f.symm a), AlgEquiv.apply_symm_apply]
  simp only [lowerRamificationGroup, ofAdd_sub, ofAdd_neg, Subtype.forall, Subgroup.mem_mk,
    Set.mem_setOf_eq, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply]
  constructor <;>
  intro h <;>
  constructor <;>
  intro a ha
  constructor <;> intro h'
  · simp only [comap_apply, RingHom.coe_coe, AlgEquiv.trans_apply]
    rw [← hf _, ← hf _]
    apply (h.1 (f.symm a) (f.symm ha)).1
    rw [hf' _, hf' _]
    exact h'
  · rw [← hf' _, ← hf' _]
    apply (h.1 (f.symm a) (f.symm ha)).2
    simp only [comap_apply, RingHom.coe_coe]
    rw [hf _, hf _]
    exact h'
   -- need theorem/def of lift of f to integer is isom
  · nth_rw 2 [← AlgEquiv.symm_apply_apply f.symm a]
    simp only [AlgEquiv.symm_symm]
    rw [← _root_.map_sub f (s (f.symm a)) (f.symm a), ← hf _]
    apply h.2
    apply (mem_integer_iff _ _).2
    rw [hf' _]
    exact ha
  · constructor <;> intro hs'
    · simp only [comap_apply, RingHom.coe_coe]
      rw [hf _, hf _, ← AlgEquiv.symm_apply_apply f a, ← AlgEquiv.symm_apply_apply f ha]
      apply (h.1 (f a) (f ha)).1
      rw [← hf _, ← hf _]
      exact hs'
    · simp only [comap_apply, RingHom.coe_coe, hf _, hf _] at hs'
      rw [← AlgEquiv.symm_apply_apply f a, ← AlgEquiv.symm_apply_apply f ha] at hs'
      rw [hf _, hf _]
      apply (h.1 (f a) (f ha)).2 hs'
  · rw [hf _, _root_.map_sub, ← AlgEquiv.symm_apply_apply f a]
    nth_rw 2 [AlgEquiv.symm_apply_apply]
    apply h.2
    apply (mem_integer_iff _ _).2
    rw [← hf _]
    exact ha

end autCongr

section WithBot
-- this should be put into a suitable place, Also add `WithOne`? `WithTop`, `WithBot`, `WithOne`, `Multiplicative`, `Additive`
open Classical
-- there is no `ConditionallyCompleteLinearOrderTop` in mathlib ...
-- # The definition of `WithTop.instInfSet` have to be changed （done in latest version）
#check WithBot.linearOrder
noncomputable instance {α} [ConditionallyCompleteLinearOrder α] : ConditionallyCompleteLinearOrderBot (WithBot α) where
  toConditionallyCompleteLattice := WithBot.conditionallyCompleteLattice
  le_total := WithBot.linearOrder.le_total
  decidableLE := WithBot.decidableLE
  decidableEq := WithBot.decidableEq
  decidableLT := WithBot.decidableLT
  csSup_of_not_bddAbove s h := by
    rw [WithBot.sSup_empty]
    simp only [sSup, sInf, Set.subset_singleton_iff]
    by_cases hs : ∀ y ∈ s, y = (⊤ : WithTop αᵒᵈ)
    · rw [if_pos (Or.inl hs)]; rfl
    · rw [show (⊤ : WithTop αᵒᵈ) = (⊥ : WithBot α) by rfl, ite_eq_left_iff]
      intro h1
      push_neg at h1
      exfalso
      exact h h1.2
  csInf_of_not_bddBelow s h := by
    exfalso
    exact h (OrderBot.bddBelow s)
  bot_le := WithBot.orderBot.bot_le
  csSup_empty := by simp only [WithBot.sSup_empty]

noncomputable instance {α} [ConditionallyCompleteLinearOrder α] : ConditionallyCompleteLinearOrderBot (WithZero α) := inferInstanceAs (ConditionallyCompleteLinearOrderBot (WithBot α))

instance {α} [Add α] [ConditionallyCompleteLinearOrder α] : ConditionallyCompleteLinearOrder (Multiplicative α) := inferInstanceAs (ConditionallyCompleteLinearOrder α)

-- noncomputable instance : ConditionallyCompleteLinearOrderBot ℤₘ₀ := inferInstanceAs (ConditionallyCompleteLinearOrderBot (WithZero ℤ))

end WithBot

section lowerIndex

variable (R S : Type*) [CommRing R] [Ring S] [vS : Valued S ℤₘ₀] [Algebra R S]


open Classical
-- 0 if lower than 0
-- we define the lower index of ramification groups of ring extension S/R i_[S/R] : Gal(S/R) → ℕ∞ (ℕ∞ is somehow conflict with ℤₘ₀, it causes some extra coercion), i_[S/R] s = sup_{x} v (s (x) - x)
noncomputable def AlgEquiv.lowerIndex (s : S ≃ₐ[R] S) : ℕ∞ :=
  if h : ⨆ x : vS.v.integer, vS.v (s x - x) = 0 then ⊤
  else (- Multiplicative.toAdd (WithZero.unzero h)).toNat

scoped [Valued] notation:max " i_[" S:max "/" R:max "]" => AlgEquiv.lowerIndex R S


-- translate the type of lowerIndex from ℕ∞ to ℚ
noncomputable def AlgEquiv.truncatedLowerIndex (u : ℚ) (s : (S ≃ₐ[R] S)) : ℚ :=
  if h : i_[S/R] s = ⊤ then u
  else min u ((i_[S/R] s).untop h)

scoped [Valued] notation:max " i_[" L:max "/" K:max "]ₜ" => AlgEquiv.truncatedLowerIndex K L

section lowerIndex_inequality

variable {R S}

/-- One of `val_map_sub_le_one` and `sub_self_mem_integer` should be thrown away.-/
theorem sub_self_mem_integer {s : S ≃ₐ[R] S} (hs' : s ∈ decompositionGroup R S)
  (x : vS.v.integer) :
    s x - x ∈ vS.v.integer := by
  apply Subring.sub_mem
  · rw [mem_integer_iff, val_map_le_one_iff hs']; exact x.2
  · exact x.2

/-- One of `val_map_sub_le_one` and `sub_self_mem_integer` should be thrown away.-/
theorem val_map_sub_le_one {s : S ≃ₐ[R] S} (hs' : s ∈ decompositionGroup R S)
  (x : vS.v.integer) :
    v (s x - x) ≤ 1 := sub_self_mem_integer hs' x

--if sup_{x ∈ S| v (x) ≤ 1} v (s (x) - x) ≠ ∞, sup_{x ∈ S| v (x) ≤ 1} v (s (x) - x) > 0
--is trivil in math, but is important in Lean and our project.
theorem toAdd_iSup_val_map_sub_le_zero_of_ne_zero {s : S ≃ₐ[R] S} (hs' : s ∈ decompositionGroup R S)
  (h : ⨆ x : vS.v.integer, vS.v (s x - x) ≠ 0) :
    Multiplicative.toAdd (WithZero.unzero h) ≤ 0 := by
  change (WithZero.unzero h) ≤ 1
  suffices ⨆ x : vS.v.integer, vS.v (s x - x) ≤ 1 from by
    rw [← WithZero.coe_le_coe, WithZero.coe_unzero h]
    exact this
  apply ciSup_le <| val_map_sub_le_one hs'

section adjoin_singleton

variable {K L : Type*} [Field K] [Field L]
[vK : Valued K ℤₘ₀] [vL : Valued L ℤₘ₀] [Algebra K L] [IsValExtension K L]

/-- Should be strenthened to ` > 0`-/--??-/
--suppose the generator of 𝒪[L] as a 𝒪[K]-algebra exists.
theorem decomp_val_map_generator_sub_ne_zero {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤)
  {s : L ≃ₐ[K] L} (hs' : s ∈ decompositionGroup K L) (hs : s ≠ .refl) :
    vL.v (s gen - gen) ≠ 0 := by
  by_contra h
  rw [zero_iff, sub_eq_zero] at h
  apply hs
  rw [elem_decompositionGroup_eq_iff_ValuationSubring' hs' (refl_mem_decompositionGroup K L)]
  apply Algebra.algHomClass_ext_generator hgen
  ext
  rw [DecompositionGroup.restrictValuationSubring_apply' hs',
    DecompositionGroup.restrictValuationSubring_apply' (refl_mem_decompositionGroup K L),
    h, AlgEquiv.coe_refl, id_eq]

open Polynomial in
theorem decomp_val_map_sub_le_generator {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) {s : L ≃ₐ[K] L} (hs' : s ∈ decompositionGroup K L) (x : 𝒪[L]) : v (s x - x) ≤ v (s gen - gen) := by sorry
  -- by_cases hs : s = .refl
  -- · subst hs
  --   simp only [AlgEquiv.coe_refl, id_eq, sub_self, _root_.map_zero, le_refl]
  -- rcases Algebra.exists_eq_aeval_generator hgen x with ⟨f, hf⟩
  -- subst hf
  -- rcases taylor_order_zero_apply_aeval f gen ((DecompositionGroup.restrictValuationSubring' hs') gen - gen) with ⟨b, hb⟩
  -- rw [add_sub_cancel, add_comm, ← sub_eq_iff_eq_add, aeval_algHom_apply, Subtype.ext_iff] at hb
  -- simp only [AddSubgroupClass.coe_sub, DecompositionGroup.restrictValuationSubring_apply' hs', Submonoid.coe_mul, Subsemiring.coe_toSubmonoid, Subring.coe_toSubsemiring] at hb
  -- rw [hb, Valuation.map_mul]
  -- nth_rw 2 [← mul_one (v (s gen - gen))]
  -- rw [mul_le_mul_left₀]
  -- · exact b.2
  -- · apply decomp_val_map_generator_sub_ne_zero hgen hs' hs

--sup_{x ∈ S | v x ≤ 1} v (s (x) - x) = v (s gen - gen)
theorem decomp_iSup_val_map_sub_eq_generator {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) {s : L ≃ₐ[K] L} (hs' : s ∈ decompositionGroup K L) :
  ⨆ x : vL.v.integer, v (s x - x) = v (s gen - gen) := by
  apply le_antisymm
  · letI : Nonempty 𝒪[L] := inferInstanceAs (Nonempty vL.v.integer)
    apply ciSup_le <| decomp_val_map_sub_le_generator hgen hs'
  · apply le_ciSup (f := fun (x : 𝒪[L]) ↦ v (s x - x)) _ gen
    use v (s gen - gen)
    intro y hy
    simp only [Set.mem_range, Subtype.exists, exists_prop] at hy
    rcases hy with ⟨a, ha⟩
    rw [← ha.2, show s a - a = s (⟨a, ha.1⟩ : 𝒪[L]) - (⟨a, ha.1⟩ : 𝒪[L]) by rfl]
    apply decomp_val_map_sub_le_generator hgen hs'


end adjoin_singleton

end lowerIndex_inequality

end lowerIndex

section ScalarTower

variable {R : Type*} {R' S: Type*} {ΓR ΓS ΓA ΓB : outParam Type*} [CommRing R] [CommRing R'] [Ring S]
[vS : Valued S ℤₘ₀]
[Algebra R S] [Algebra R R'] [Algebra R' S] [IsScalarTower R R' S]

@[simp]
theorem lowerIndex_refl : (i_[S/R] .refl) = ⊤ := by
  simp only [AlgEquiv.lowerIndex, AlgEquiv.coe_refl, id_eq, sub_self, _root_.map_zero, ciSup_const,
    ↓reduceDIte]

@[simp]
theorem truncatedLowerIndex_refl (u : ℚ) : AlgEquiv.truncatedLowerIndex R S u .refl = u := by
  simp only [AlgEquiv.truncatedLowerIndex, lowerIndex_refl, ↓reduceDIte]

section lowerIndex_inequality

section K_not_field

variable {K K' L : Type*} {ΓK ΓK' : outParam Type*} [CommRing K] [Field K'] [Field L] [LinearOrderedCommGroupWithZero ΓK]
[LinearOrderedCommGroupWithZero ΓK'] [vL : Valued L ℤₘ₀] [Algebra K L]
[Algebra K K'] [Algebra K' L] [IsScalarTower K K' L]

/-- Another version where `𝒪[L] is finite over 𝒪[K]` -/
theorem lowerIndex_ne_one {s : L ≃ₐ[K] L} (hs' : s ∈ decompositionGroup K L) (hs : s ≠ .refl) : i_[L/K] s ≠ ⊤ := by
  intro heq
  simp only [AlgEquiv.lowerIndex, AddSubgroupClass.coe_sub,
    dite_eq_left_iff, ENat.coe_ne_top, imp_false, not_not] at heq
  have hL : ∀ x : vL.v.integer, s x = x := by
    intro x
    apply le_of_eq at heq
    rw [← sub_eq_zero, ← Valuation.zero_iff vL.v, show (0 : ℤₘ₀) = ⊥ by rfl, eq_bot_iff]
    refine (ciSup_le_iff' ?_).mp heq x
    use 1
    intro a ha
    rcases ha with ⟨y, hy⟩
    rw [← hy]
    exact sub_self_mem_integer hs' _
  apply hs
  ext x
  rcases ValuationSubring.mem_or_inv_mem vL.v.valuationSubring x with h | h
  · exact hL ⟨x, h⟩
  · calc
    _ = (s x⁻¹)⁻¹ := by simp only [inv_inv, map_inv₀]
    _ = _ := by rw [hL ⟨x⁻¹, h⟩, inv_inv, AlgEquiv.coe_refl, id_eq]

@[simp]
theorem lowerIndex_eq_top_iff_eq_refl {s : L ≃ₐ[K] L} (hs' : s ∈ decompositionGroup K L) : i_[L/K] s = ⊤ ↔ s = .refl := by
  constructor <;> intro h
  · contrapose! h
    apply lowerIndex_ne_one hs' h
  · simp only [h, lowerIndex_refl]

theorem iSup_val_map_sub_eq_zero_iff_eq_refl {s : L ≃ₐ[K] L} (hs' : s ∈ decompositionGroup K L) :
  ⨆ x : vL.v.integer, vL.v (s x - x) = 0 ↔ s = .refl := by
  rw [← lowerIndex_eq_top_iff_eq_refl]
  simp only [AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe, AlgEquiv.lowerIndex, dite_eq_left_iff, ENat.coe_ne_top, imp_false, Decidable.not_not]
  exact hs'

end K_not_field

--K_is_Valued_field
section K_is_field

variable {K L : Type*} [Field K] [Field L]
[vK : Valued K ℤₘ₀] [vL : Valued L ℤₘ₀] [Algebra K L] [IsValExtension K L]

theorem mem_lowerRamificationGroup_of_le_neg_one {s : L ≃ₐ[K] L} (hs : s ∈ decompositionGroup K L) {u : ℤ} (hu : u ≤ -1) : s ∈ G(L/K)_[u] := by
  unfold lowerRamificationGroup
  simp only [ofAdd_sub, ofAdd_neg, Subtype.forall, Subgroup.mem_mk, Set.mem_setOf_eq]
  constructor
  · exact hs
  · intro a ha
    apply le_trans (val_map_sub_le_one hs ⟨a, ha⟩)
    simp only [WithZero.one_le_coe, one_le_div', le_inv_iff_mul_le_one_left, ← ofAdd_add]
    refine Multiplicative.toAdd_le.mp ?_
    simp only [ofAdd_add, toAdd_mul, toAdd_ofAdd, toAdd_one]
    linarith [hu]

-- the type of `n` should be changed
-- instead, change when use this theorem
open Multiplicative in
theorem mem_lowerRamificationGroup_iff_of_generator
  {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤)
  {s : L ≃ₐ[K] L} (hs' : s ∈ decompositionGroup K L) (n : ℕ) :
    s ∈ G(L/K)_[n] ↔ n + 1 ≤ i_[L/K] s := by
  simp only [lowerRamificationGroup, Subtype.forall, Subgroup.mem_mk,
    Set.mem_setOf_eq, AlgEquiv.lowerIndex]
  by_cases hrefl : s = .refl
  · simp only [hrefl, AlgEquiv.coe_refl, id_eq, sub_self, _root_.map_zero, ofAdd_sub, ofAdd_neg,
    zero_le', implies_true, and_true, ciSup_const, ↓reduceDIte, le_top, iff_true]
    exact refl_mem_decompositionGroup K L
  · have hne0 : ¬ ⨆ x : vL.v.integer, vL.v (s x - x) = 0 := by
      rw [iSup_val_map_sub_eq_zero_iff_eq_refl hs']; exact hrefl
    constructor
    · intro ⟨_, hs⟩
      simp only [hne0, ↓reduceDIte, ge_iff_le]
      rw [show (n : ℕ∞) + 1 = (n + 1 : ℕ) by rfl, ← ENat.some_eq_coe, WithTop.coe_le_coe,
        Int.le_toNat (by simp only [Left.nonneg_neg_iff, toAdd_iSup_val_map_sub_le_zero_of_ne_zero hs']),
        le_neg]
      change _ ≤ toAdd (ofAdd (-(n + 1) : ℤ))
      rw [toAdd_le]
      /- The following part should be extracted.
      It is also used in `toAdd_iSup_val_map_sub_le_zero_of_ne_zero`. -/
      suffices ⨆ x : vL.v.integer, vL.v (s x - x) ≤ ofAdd (-(n + 1) : ℤ) from by
        rw [← WithZero.coe_le_coe, WithZero.coe_unzero hne0]
        exact this
      apply ciSup_le
      /- end -/
      intro x
      rw [neg_add']
      exact hs x.1 x.2
    · intro h
      simp only [hs', true_and]
      simp only [hne0, ↓reduceDIte] at h
      rw [show (n : ℕ∞) + 1 = (n + 1 : ℕ) by rfl, ← ENat.some_eq_coe, WithTop.coe_le_coe,
        Int.le_toNat (by simp only [Left.nonneg_neg_iff, toAdd_iSup_val_map_sub_le_zero_of_ne_zero hs']),
        le_neg] at h
      change _ ≤ toAdd (ofAdd (-(n + 1) : ℤ)) at h
      rw [toAdd_le, ← WithZero.coe_le_coe, WithZero.coe_unzero hne0, neg_add'] at h
      intro x hx
      apply le_trans _ h
      apply le_ciSup (f := fun (x : vL.v.integer) ↦ v (s x - x)) _ ⟨x, hx⟩
      use v (s gen - gen)
      intro a
      simp only [Set.mem_range, Subtype.exists, exists_prop, forall_exists_index, and_imp]
      intro x hx heq
      rw [← heq]
      apply decomp_val_map_sub_le_generator hgen hs' ⟨x, hx⟩


theorem mem_lowerRamificationGroup_of_le_truncatedLowerIndex_sub_one {s : L ≃ₐ[K] L} (hs' : s ∈ decompositionGroup K L) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) {u r : ℚ} (h : u ≤ i_[L/K]ₜ r s - 1) : s ∈ G(L/K)_[⌈u⌉] := by
  unfold AlgEquiv.truncatedLowerIndex at h
  by_cases hu : u ≤ -1
  · apply mem_lowerRamificationGroup_of_le_neg_one hs'
    exact Int.ceil_le.mpr hu
  · push_neg at hu
    have hu' : ⌈u⌉.toNat = ⌈u⌉ := by
      apply Int.toNat_of_nonneg
      apply Int.le_ceil_iff.2
      simp only [Int.cast_zero, zero_sub, hu]
    by_cases hs : i_[L/K] s = ⊤
    · simp [hs] at h
      --maybe there is a better way
      have : (⌈u⌉.toNat + 1) ≤ i_[L/K] s := by simp [hs]
      convert (mem_lowerRamificationGroup_iff_of_generator hgen hs' ⌈u⌉.toNat).2 this
      rw [hu']
    · simp [hs] at h
      have : (⌈u⌉.toNat + 1) ≤ i_[L/K] s := by
        have h' : u + 1 ≤ min r ↑(WithTop.untop (i_[L/K] s) hs) := by linarith [h]
        rw [← WithTop.coe_untop (i_[L/K] s) hs]
        convert (le_min_iff.1 h').right
        constructor <;> intro hle
        · -- there might be a better way, it's too long :(
          have : u + 1 ≤ ⌈u⌉.toNat + 1 := by
            simp only [add_le_add_iff_right]
            apply le_trans (Int.le_ceil u)
            rw [← Int.cast_natCast]
            simp only [Int.ofNat_toNat, Int.cast_max, Int.cast_zero, le_max_iff, le_refl, Int.cast_nonpos, true_or]
          simp only [← Nat.cast_one (R := ℕ∞), ← Nat.cast_add] at hle
          apply WithTop.coe_le_coe.1 at hle
          apply le_trans this
          simp only [← Nat.cast_one (R := ℚ), ← Nat.cast_add]
          norm_cast
        · simp only [← Nat.cast_one (R := ℕ∞), ← Nat.cast_add]
          apply WithTop.coe_le_coe.2
          simp only [Nat.cast_add, Nat.cast_id, Nat.cast_one]
          apply Int.ceil_le.2 at hle
          rw [Int.ceil_add_one, ← hu'] at hle
          exact Int.ofNat_le.mp hle
      convert (mem_lowerRamificationGroup_iff_of_generator hgen hs' ⌈u⌉.toNat).2 this
      exact Eq.symm hu'

variable [IsDiscrete vK.v] [IsDiscrete vL.v] [IsValExtension K L] [CompleteSpace K] [FiniteDimensional K L]

theorem le_truncatedLowerIndex_sub_one_iff_mem_lowerRamificationGroup (s : L ≃ₐ[K] L) (u : ℚ) (r : ℚ) (h : u + 1 ≤ r) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : u ≤ i_[L/K]ₜ r s - 1 ↔ s ∈ G(L/K)_[⌈u⌉] := by
  by_cases hu : u ≤ -1
  · constructor <;> intro hu'
    · apply mem_lowerRamificationGroup_of_le_neg_one
      rw [decompositionGroup_eq_top]
      apply Subgroup.mem_top
      apply Int.ceil_le.2
      simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one]
      apply hu
    · unfold AlgEquiv.truncatedLowerIndex
      by_cases hc : i_[L/K] s = ⊤
      · simp only [hc, ↓reduceDIte]
        linarith
      · simp only [hc, ↓reduceDIte]
        by_cases hr : r ≤ (WithTop.untop (i_[L/K] s) hc)
        · rw [min_eq_left hr]
          linarith
        · push_neg at hr
          rw [min_eq_right (le_of_lt hr)]
          have : 0 ≤ ((WithTop.untop (i_[L/K] s) hc : ℕ) : ℚ) := Nat.cast_nonneg' (WithTop.untop ( i_[L/K] s) hc)
          linarith
  · push_neg at hu
    have hu' : ⌈u⌉.toNat = ⌈u⌉ := by
      apply Int.toNat_of_nonneg
      apply Int.le_ceil_iff.2
      simp only [Int.cast_zero, zero_sub, hu]
    constructor
    · apply mem_lowerRamificationGroup_of_le_truncatedLowerIndex_sub_one _ hgen
      rw [decompositionGroup_eq_top]
      apply Subgroup.mem_top
    · intro hs
      have h1 : (⌈u⌉.toNat + 1) ≤ i_[L/K] s := by
        apply (mem_lowerRamificationGroup_iff_of_generator hgen ?_ ⌈u⌉.toNat).1
        --the type of N and Z make some truble
        rw [hu']
        exact hs
        rw [decompositionGroup_eq_top]
        apply Subgroup.mem_top
      unfold AlgEquiv.truncatedLowerIndex
      by_cases hc : i_[L/K] s = ⊤
      · simp [hc]
        linarith [h]
      · simp [hc]
        have hle : u + 1 ≤ min r ↑(WithTop.untop ( i_[L/K] s) (of_eq_false (eq_false hc) : ¬ i_[L/K] s = ⊤)) := by
          apply le_min_iff.2
          constructor
          · exact h
          · have hle' : u + 1 ≤ ⌈u⌉.toNat + 1 := by
              simp only [add_le_add_iff_right]
              apply le_trans (Int.le_ceil u)
              rw [← Int.cast_natCast]
              simp only [Int.ofNat_toNat, Int.cast_max, Int.cast_zero, le_max_iff, le_refl, Int.cast_nonpos, true_or]
            apply le_trans hle'
            rw [← Nat.cast_one, ← Nat.cast_add]
            apply Nat.mono_cast
            exact (WithTop.le_untop_iff (of_eq_false (eq_false hc))).mpr h1
        linarith [hle]



end K_is_field

end lowerIndex_inequality
--independent of the existence of the generator of ring ext.
@[simp]
theorem lowerIndex_restrictScalars (s : S ≃ₐ[R'] S) : i_[S/R] (s.restrictScalars R) =  i_[S/R'] s := rfl

@[simp]
theorem truncatedLowerIndex_restrictScalars (u : ℚ) (s : S ≃ₐ[R'] S) : i_[S/R]ₜ u (s.restrictScalars R) = i_[S/R']ₜ u s := rfl

@[simp]
theorem lowerRamificationGroup_restrictScalars (u : ℤ) : G(S/R)_[u].comap (AlgEquiv.restrictScalarsHom R) = G(S/R')_[u] := rfl

end ScalarTower

section ExhausiveSeperated

section lower_eq_decomp

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
    _ ≤ 1 := max_le ((val_map_le_one_iff hs a).mpr ha) ha
    _ ≤ _ := by
      show (.coe (0 : ℤ) : ℤₘ₀) ≤ .coe ((- u - 1) : ℤ)
      norm_cast
      show (0 : ℤ) ≤ - u - 1
      linarith

end lower_eq_decomp

section eq_top

variable {K L : Type*} [Field K] [Field L] [vK : Valued K ℤₘ₀] [IsDiscrete vK.v] [vL : Valued L ℤₘ₀] [Algebra K L] [FiniteDimensional K L]

theorem lowerRamificationGroup_eq_top [IsValExtension K L] [CompleteSpace K] {u : ℤ} (h : u ≤ -1) : G(L/K)_[u] = ⊤ := by
  rw [lowerRamificationGroup_eq_decompositionGroup h, decompositionGroup_eq_top]

end eq_top

section eq_bot

open ExtDVR IsValExtension Polynomial

-- `IsDiscrete vK.v` may be weakened to `Nontrivial vK.v`.
variable (K L : Type*) [Field K] [Field L] [vK : Valued K ℤₘ₀] [IsDiscrete vK.v] [vL : Valued L ℤₘ₀] [IsDiscrete vL.v] [Algebra K L] [IsValExtension K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

variable {K L}
variable [CompleteSpace K]

theorem AlgEquiv.mem_decompositionGroup [CompleteSpace K] (s : L ≃ₐ[K] L) : s ∈ decompositionGroup K L := by
  rw [decompositionGroup_eq_top]
  exact Subgroup.mem_top s

--it's already in ValExtension
instance : IsLocalHom (algebraMap 𝒪[K] 𝒪[L]) where
    map_nonunit r hr := by
      by_cases h : r = 0
      · simp [h] at hr
      · apply Valuation.Integers.isUnit_of_one (v := vK.v)
        · exact Valuation.integer.integers (v := vK.v)
        · simpa only [Algebra.algebraMap_ofSubring_apply, isUnit_iff_ne_zero, ne_eq,
          ZeroMemClass.coe_eq_zero]
        · apply Valuation.Integers.one_of_isUnit (Valuation.integer.integers (v := vL.v)) at hr
          change v (((algebraMap ↥𝒪[K] ↥𝒪[L]) r) : L) = 1 at hr
          norm_cast at hr
          simp only [IsValExtension.val_map_eq_one_iff] at hr
          exact hr

instance : Module.Finite 𝒪[K] 𝒪[L] := Module.IsNoetherian.finite 𝒪[K] 𝒪[L]

set_option synthInstance.maxHeartbeats 1000000

theorem AlgEquiv.Simple_Extension_of_CDVR [CompleteSpace K] [Algebra.IsSeparable (LocalRing.ResidueField 𝒪[K]) (LocalRing.ResidueField 𝒪[L])] : ∃ gen : 𝒪[L], Algebra.adjoin 𝒪[K] {gen} = ⊤ := ExtDVR.exists_primitive (A := 𝒪[K]) (B := 𝒪[L]) (integerAlgebra_injective K L)


--can delete the assumption of generator.
/-- Should be strenthened to ` > 0`-/
theorem AlgEquiv.val_map_generator_sub_ne_zero {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) {s : L ≃ₐ[K] L} (hs : s ≠ .refl) : vL.v (s gen - gen) ≠ 0 := by
  by_contra h
  rw [zero_iff, sub_eq_zero] at h
  apply hs
  rw [AlgEquiv.eq_iff_ValuationSubring]
  apply Algebra.algHomClass_ext_generator hgen
  ext; simp only [AlgEquiv.restrictValuationSubring_apply, h, AlgEquiv.coe_refl, id_eq]

/--  The orginal proof uses `PowerBasis.adjoin_gen_eq_top`.
Should be strenthened to ` > 0`-/
theorem AlgEquiv.val_map_powerBasis_sub_ne_zero (pb : PowerBasis 𝒪[K] 𝒪[L]) {s : L ≃ₐ[K] L} (hs : s ≠ .refl) :
  vL.v (s pb.gen - pb.gen) ≠ 0 :=
  s.val_map_generator_sub_ne_zero (PowerBasis.adjoin_gen_eq_top pb) hs

open Polynomial in
theorem AlgEquiv.val_map_sub_le_generator {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) (s : L ≃ₐ[K] L) (x : 𝒪[L]) : v (s x - x) ≤ v (s gen - gen) := by
  sorry
  -- by_cases hs : s = .refl
  -- · subst hs
  --   simp only [AlgEquiv.coe_refl, id_eq, sub_self, _root_.map_zero, le_refl]
  -- rcases Algebra.exists_eq_aeval_generator hgen x with ⟨f, hf⟩
  -- subst hf
  -- rcases taylor_order_zero_apply_aeval f gen ((AlgEquiv.restrictValuationSubring s) gen - gen) with ⟨b, hb⟩
  -- rw [add_sub_cancel, add_comm, ← sub_eq_iff_eq_add, aeval_algHom_apply, Subtype.ext_iff] at hb
  -- simp only [AddSubgroupClass.coe_sub, AlgEquiv.restrictValuationSubring_apply, Submonoid.coe_mul, Subsemiring.coe_toSubmonoid, Subring.coe_toSubsemiring] at hb
  -- rw [hb, Valuation.map_mul]
  -- nth_rw 2 [← mul_one (v (s gen - gen))]
  -- rw [mul_le_mul_left₀]
  -- · exact b.2
  -- · apply AlgEquiv.val_map_generator_sub_ne_zero hgen hs

open Polynomial in
/-- The orginal proof uses `PowerBasis.exists_eq_aeval`. -/
theorem AlgEquiv.val_map_sub_le_powerBasis (pb : PowerBasis 𝒪[K] 𝒪[L]) (s : L ≃ₐ[K] L) (x : 𝒪[L]) : vL.v (s x - x) ≤ vL.v (s pb.gen - pb.gen) := AlgEquiv.val_map_sub_le_generator (PowerBasis.adjoin_gen_eq_top pb) s x

theorem AlgEquiv.iSup_val_map_sub_eq_generator {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) (s : L ≃ₐ[K] L) :
  ⨆ x : vL.v.integer, v (s x - x) = v (s gen - gen) := by
  apply le_antisymm
  · letI : Nonempty 𝒪[L] := inferInstanceAs (Nonempty vL.v.integer)
    apply ciSup_le <| AlgEquiv.val_map_sub_le_generator hgen s
  · apply le_ciSup (f := fun (x : 𝒪[L]) ↦ v (s x - x)) _ gen
    use v (s gen - gen)
    intro y hy
    simp only [Set.mem_range, Subtype.exists, exists_prop] at hy
    rcases hy with ⟨a, ha⟩
    rw [← ha.2, show s a - a = s (⟨a, ha.1⟩ : 𝒪[L]) - (⟨a, ha.1⟩ : 𝒪[L]) by rfl]
    apply AlgEquiv.val_map_sub_le_generator hgen

/-- The original proof uses `AlgEquiv.val_map_sub_le_powerBasis`. -/
theorem AlgEquiv.iSup_val_map_sub_eq_powerBasis (pb : PowerBasis 𝒪[K] 𝒪[L]) (s : L ≃ₐ[K] L) :
  ⨆ x : vL.v.integer, v (s x - x) = v (s pb.gen - pb.gen) :=
  AlgEquiv.iSup_val_map_sub_eq_generator (PowerBasis.adjoin_gen_eq_top pb) s

open Classical in
/-- Should I `open Classical`? -/
theorem lowerIndex_of_powerBasis (pb : PowerBasis 𝒪[K] 𝒪[L]) (s : L ≃ₐ[K] L) :
  i_[L/K] s = if h : s = .refl then (⊤ : ℕ∞)
    else (- Multiplicative.toAdd (WithZero.unzero (AlgEquiv.val_map_powerBasis_sub_ne_zero pb h))).toNat := by
  by_cases h : s = .refl
  · simp only [h, lowerIndex_refl, ↓reduceDIte]
  · unfold AlgEquiv.lowerIndex
    simp only [h, AlgEquiv.iSup_val_map_sub_eq_powerBasis pb, AlgEquiv.val_map_powerBasis_sub_ne_zero pb h, ↓reduceDIte]

@[simp]
theorem lowerIndex_ne_refl {s : L ≃ₐ[K] L} (hs : s ≠ .refl) : i_[L/K] s ≠ ⊤ := by
  apply lowerIndex_ne_one
  rw [decompositionGroup_eq_top]
  apply Subgroup.mem_top s
  exact hs

variable (K L) in
theorem iSup_ne_refl_lowerIndex_ne_top [Nontrivial (L ≃ₐ[K] L)] :
  ⨆ s : {s : (L ≃ₐ[K] L) // s ≠ .refl}, i_[L/K] s ≠ ⊤ := by
  rw [← lt_top_iff_ne_top, iSup_lt_iff]
  let f : {s : (L ≃ₐ[K] L) // s ≠ .refl} → ℕ :=
    fun s ↦ WithTop.untop _ (lowerIndex_ne_refl s.2)
  letI : Nonempty {s : (L ≃ₐ[K] L) // s ≠ .refl} := Exists.casesOn (exists_ne AlgEquiv.refl)
    fun s hs ↦ Nonempty.intro ⟨s, hs⟩
  rcases Finite.exists_max f with ⟨a, ha⟩
  use f a
  constructor
  · exact WithTop.coe_lt_top _
  · intro s
    have : i_[L/K] s = f s := by
      rw [← ENat.some_eq_coe, WithTop.coe_untop]
    simp only [ne_eq, this, Nat.cast_le, ha]

-- if n > sup_{s ≠ 1} i_G s then G_n = {1}.
theorem aux7 [Algebra.IsSeparable K L] [Algebra (LocalRing.ResidueField 𝒪[K]) (LocalRing.ResidueField 𝒪[L])] [Algebra.IsSeparable (LocalRing.ResidueField 𝒪[K]) (LocalRing.ResidueField 𝒪[L])]
  {n : ℕ} (hu : n > ⨆ s : {s : (L ≃ₐ[K] L) // s ≠ .refl}, i_[L/K] s)
  {s : L ≃ₐ[K] L} (hs : s ∈ G(L/K)_[n]) : s = .refl := by
  apply (mem_lowerRamificationGroup_iff_of_generator (PowerBasis.adjoin_gen_eq_top (PowerBasisValExtension K L)) s.mem_decompositionGroup n).mp at hs
  by_contra! h
  rw [ENat.add_one_le_iff (by simp only [ne_eq, ENat.coe_ne_top, not_false_eq_true])] at hs
  have : i_[L/K] s < n := by
    apply lt_of_le_of_lt _ hu
    rw [show s = (⟨s, h⟩ : {s // s ≠ .refl}).1 by rfl]
    apply le_iSup (fun (x : {s // s ≠ .refl}) => i_[L/K] x) (⟨s, h⟩ : {s // s ≠ .refl})
  apply lt_asymm hs this

-- this uses local fields and bichang's work, check if the condition is too strong..., It should be O_L is finitely generated over O_K
theorem exist_lowerRamificationGroup_eq_bot [CompleteSpace K] [Algebra.IsSeparable K L] [Algebra (LocalRing.ResidueField 𝒪[K]) (LocalRing.ResidueField 𝒪[L])]
  [Algebra.IsSeparable (LocalRing.ResidueField 𝒪[K]) (LocalRing.ResidueField 𝒪[L])] :
    ∃ u : ℤ, G(L/K)_[u] = ⊥ := by
  by_cases h : Nontrivial (L ≃ₐ[K] L)
  · use (WithTop.untop _ (iSup_ne_refl_lowerIndex_ne_top K L) : ℕ) + 1
    rw [eq_bot_iff]
    intro s hs
    rw [Subgroup.mem_bot, AlgEquiv.aut_one, aux7 _ hs]
    rw [← ENat.some_eq_coe]
    simp only [WithTop.coe_add, WithTop.coe_untop, WithTop.coe_one, gt_iff_lt]
    nth_rw 1 [← add_zero (⨆ s : {s : (L ≃ₐ[K] L) // s ≠ .refl}, i_[L/K] s)]
    have : (0 : ℕ∞) < 1 := by
      rw [← ENat.coe_one, ← ENat.some_eq_coe, WithTop.coe_pos]
      exact zero_lt_one
    convert WithTop.add_lt_add_left (iSup_ne_refl_lowerIndex_ne_top K L) this
  · use 0
    rw [eq_bot_iff]
    intro s _
    rw [Subgroup.mem_bot, AlgEquiv.aut_one]
    letI : Subsingleton (L ≃ₐ[K] L) := not_nontrivial_iff_subsingleton.mp h
    apply Subsingleton.allEq

variable [LocalField K] [LocalField L] [Algebra.IsSeparable K L]

end eq_bot

end ExhausiveSeperated

section sum_lowerIndex
#check lowerIndex_of_powerBasis
#check PowerBasisValExtension


open LocalField

variable {K M L : Type*} [Field K] [Field M] [Field L]
[Algebra K L] [Algebra K M] [Algebra M L]
[Normal K L]
[IsScalarTower K M L]
[FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional M L]
[Normal K M]
[vK : Valued K ℤₘ₀] [IsDiscrete vK.v]
[vM : Valued M ℤₘ₀] [IsDiscrete vM.v]
[vL : Valued L ℤₘ₀] [IsDiscrete vL.v]
[IsValExtension K L] [IsValExtension M L] [IsValExtension K M]
[Algebra.IsSeparable K L] [Algebra.IsSeparable M L] [Algebra.IsSeparable K M]
[CompleteSpace K] [CompleteSpace M]

-- #synth FiniteDimensional M L

#check AlgEquiv.restrictNormalHom_surjective

variable (σ : M ≃ₐ[K] M) (s : L ≃ₐ[K] L)
#check s.restrictNormal M
#check (AlgEquiv.restrictNormalHom (K₁ := L) M)⁻¹' {σ}
#synth Finite ((AlgEquiv.restrictNormalHom (K₁ := L) M)⁻¹' {σ})
#check Finset.sum

#check LocalField

--#check aux2 K L
open AlgEquiv Classical

#check Eq.subst
theorem preimage_nerefl (hsig : σ ≠ .refl) (s : L ≃ₐ[K] L) (hs : s ∈ ((restrictNormalHom M)⁻¹' {σ})) : s ≠ .refl := by
  by_contra hc
  have h : (restrictNormalHom M) (.refl (A₁ := L)) = .refl (R := K) := (restrictNormalHom M).map_one
  simp only [Set.mem_preimage, Set.mem_singleton_iff, hc, h] at hs
  absurd hsig
  exact id (Eq.symm hs)

#check AlgEquiv.val_map_powerBasis_sub_ne_zero
theorem val_mappb_sub_self_toAdd_nonpos {s : L ≃ₐ[K] L} (hs : s ≠ .refl) (x : PowerBasis 𝒪[K] 𝒪[L]) : 0 ≤ -Multiplicative.toAdd (WithZero.unzero (val_map_powerBasis_sub_ne_zero x hs)) := by
  rw [← toAdd_one, ← toAdd_inv]
  apply Multiplicative.toAdd_le.2
  apply one_le_inv'.mpr
  rw [← WithZero.coe_le_coe]
  simp only [WithZero.coe_unzero, WithZero.coe_one]
  apply val_map_sub_le_one _ x.gen
  exact mem_decompositionGroup s

-- @[coe, match_pattern] def WithZero.some {α : Type*} : α → WithTop α :=
--   Option.some

-- def addHom {α : Type*} [AddZeroClass α] : α →+ WithZero α where
--   toFun := WithTop.some
--   map_zero' := by
--     simp only [WithTop.coe_zero]
--     sorry
--   map_add' _ _ := rfl

#check Nat.cast_prod
#check WithTop.coe_sum
#check WithZero

def WithZero.some {α : Type*} : α → WithZero α :=
  Option.some

def WithZero.MulHom {α : Type*} [Monoid α] : α →* WithZero α where
  toFun := WithZero.some
  map_one' := rfl
  map_mul' _ _ := rfl


theorem WithZero.coe_prod {α β : Type*} [CommMonoid β] {s : Finset α} {f : α → β} : (↑(∏ x ∈ s, f x) : WithZero β) =  (∏ x ∈ s, ↑(f x : WithZero β)) := by
  simp only [WithZero.coe]
  apply map_prod WithZero.MulHom f s


open DiscreteValuationRing
#check Ideal.Quotient.algebraMap_quotient_pow_ramificationIdx
#check Ideal.span_singleton_pow
#check IsValExtension.coe_algebraMap_valuationSubring
theorem Valuation.prolongs_by_ramificationIndex {x : M} (hx1 : x ∈ vM.v.valuationSubring) (hx2 : (⟨x, hx1⟩ : vM.v.valuationSubring) ≠ 0) : vM.v (x) ^ ramificationIdx M L = vL.v (algebraMap M L x) := by
  obtain ⟨πL, hpiL⟩ := exists_Uniformizer_ofDiscrete vL.v
  obtain ⟨πM, hpiM⟩ := exists_Uniformizer_ofDiscrete vM.v
  obtain ⟨n1, u1, hnu1⟩ := pow_Uniformizer vM.v hx2 ⟨πM, hpiM⟩
  have ha1 : (algebraMap M L x) ∈ vL.v.valuationSubring := (mem_valuationSubring_iff v ((algebraMap M L) x)).mpr ((IsValExtension.val_map_le_one_iff x).mpr hx1)
  have ha2 : (⟨algebraMap M L x, ha1⟩ : vL.v.valuationSubring) ≠ 0 := by
    apply Subtype.coe_ne_coe.1
    simp only [ZeroMemClass.coe_zero, ne_eq, map_eq_zero]
    simp only [← ne_eq]
    apply Subtype.coe_ne_coe.2 hx2
  obtain ⟨n2, u2, hnu2⟩ := pow_Uniformizer vL.v ha2 ⟨πL, hpiL⟩
  have hirrL : Irreducible πL := by
    apply (irreducible_iff_uniformizer πL).2 (IsUniformizer_is_generator v hpiL)
  have hirrM : Irreducible πM := by
    apply (irreducible_iff_uniformizer πM).2 (IsUniformizer_is_generator v hpiM)
  simp only [SubmonoidClass.coe_pow] at hnu1 hnu2
  rw [hnu2, hnu1]
  simp only [_root_.map_mul, _root_.map_pow, val_valuationSubring_unit, mul_one]
  have hr : algebraMap M L πM ∈ vL.v.valuationSubring := by
    apply (mem_valuationSubring_iff v ((algebraMap M L) πM)).mpr
    simp only [IsValExtension.val_map_le_one_iff]
    apply (mem_valuationSubring_iff vM.v πM).mp πM.2
  have hr' : (⟨algebraMap M L πM, hr⟩ : vL.v.valuationSubring) ≠ 0 := by
    apply Subtype.coe_ne_coe.1
    simp only [ZeroMemClass.coe_zero, ne_eq, map_eq_zero]
    exact Uniformizer_ne_zero vM.v hpiM
  obtain ⟨n, u, hnu⟩ := pow_Uniformizer vL.v hr' ⟨πL,hpiL⟩
  have hrami : ramificationIdx M L = n := by
    unfold ramificationIdx LocalRing.ramificationIdx Ideal.ramificationIdx
    simp only [SubmonoidClass.coe_pow] at hnu
    have hinM : πM.1 ∈ vM.v.integer := SetLike.coe_mem πM
    have hinL : πL.1 ∈ vL.v.integer := SetLike.coe_mem πL
    have hinu : u.1.1 ∈ vL.v.integer := SetLike.coe_mem u.1
    rw [_root_.Irreducible.maximalIdeal_eq (ϖ := ⟨πM.1, hinM⟩), _root_.Irreducible.maximalIdeal_eq (ϖ := ⟨πL.1, hinL⟩)]
    rw [← IsValExtension.coe_algebraMap_valuationSubring] at hnu
    have hnu' : ((algebraMap ↥𝒪[M] ↥𝒪[L]) πM) = (⟨πL.1, hinL⟩ : vL.v.integer) ^ n * ⟨u.1, hinu⟩  := by
      apply SetLike.coe_eq_coe.mp
      simp only [IsValExtension.coe_algebraMap_integer, Subtype.coe_eta, Subring.coe_mul, SubmonoidClass.coe_pow]
      exact hnu
    have hspan : Ideal.span {πL ^ n * u.1} = Ideal.span {πL ^ n} := by
      apply Ideal.span_singleton_eq_span_singleton.2
      apply Associated.symm
      use u
    have heq : {n_1 | πL ^ n_1 ∣ πL ^ n} = {n_1 | n_1 ≤ n} := by
      ext t
      constructor <;> intro ht
      · simp only [Set.mem_setOf_eq] at ht ⊢
        have hnezero : πL ≠ 0 := by
          apply_mod_cast Uniformizer_ne_zero vL.v hpiL
        have hneunit : ¬ IsUnit πL := by
          apply Uniformizer_not_isUnit vL.v hpiL
        apply (pow_dvd_pow_iff hnezero hneunit).1
        exact ht
      · simp only [Set.mem_setOf_eq] at ht ⊢
        apply pow_dvd_pow
        exact ht
    simp only [Subtype.coe_eta, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, hnu', hspan, Ideal.span_singleton_le_span_singleton, heq]
    apply le_antisymm
    · exact csSup_le' fun ⦃a⦄ a ↦ a
    · apply le_csSup
      use n
      unfold upperBounds
      simp only [Set.mem_setOf_eq, imp_self, implies_true]
      simp only [Set.mem_setOf_eq, le_refl]
    simp only [Subtype.coe_eta]
    exact hirrL
    simp only [Subtype.coe_eta]
    exact hirrM
  simp only [SubmonoidClass.coe_pow] at hnu
  rw [hrami]
  rw [hpiM, hpiL, ← pow_mul]
  apply congrArg
  apply_fun (algebraMap M L) at hnu1
  simp only [_root_.map_mul, _root_.map_pow, hnu, hnu2, mul_pow, ← pow_mul, mul_comm, mul_assoc] at hnu1
  rw [mul_comm (πL.1 ^ (n1 * n))] at hnu1
  symm
  let u3 : (vL.v.valuationSubring)ˣ := {
    val := ⟨u.1.1 ^ n1 * (algebraMap M L) u1.1.1, by
      apply ValuationSubring.mul_mem
      · apply pow_mem u.1.2
      · refine (mem_valuationSubring_iff v ((algebraMap M L) ↑↑u1)).mpr ?_
        refine (IsValExtension.val_map_le_one_iff u1.1.1).mpr ?_
        apply (mem_valuationSubring_iff v u1.1.1).1 u1.1.2
      ⟩
    inv := ⟨(algebraMap M L) u1.1.1⁻¹ * u.1.1⁻¹ ^ n1, by
      apply ValuationSubring.mul_mem
      · refine (mem_valuationSubring_iff v ((algebraMap M L) (↑↑u1)⁻¹)).mpr ?_
        refine (IsValExtension.val_map_le_one_iff u1.1.1⁻¹).mpr ?_
        apply (mem_valuationSubring_iff v u1.1.1⁻¹).1
        have hu := u1.2.2
        have hinv : u1.1.1⁻¹ = (u1⁻¹).1.1 := by
          rw [← Units.inv_eq_val_inv]
          apply DivisionMonoid.inv_eq_of_mul u1.1.1 ↑u1.inv ?_
          exact (Submonoid.mk_eq_one v.valuationSubring.toSubmonoid).mp u1.val_inv
        rw [Units.inv_eq_val_inv] at hu
        rw [hinv]
        exact hu
      · apply pow_mem
        have hu := u.2.2
        have hinv : u.1.1⁻¹ = (u⁻¹).1.1 := by
          rw [← Units.inv_eq_val_inv]
          apply DivisionMonoid.inv_eq_of_mul u.1.1 ↑u.inv ?_
          exact (Submonoid.mk_eq_one v.valuationSubring.toSubmonoid).mp u.val_inv
        rw [Units.inv_eq_val_inv] at hu
        rw [hinv]
        exact hu
      ⟩
    val_inv := by
      simp only [map_inv₀, inv_pow, MulMemClass.mk_mul_mk, map_inv, mul_assoc]
      simp only [← mul_assoc (algebraMap M L u1.1.1), isUnit_iff_ne_zero, ne_eq, map_eq_zero, ZeroMemClass.coe_eq_zero, Units.ne_zero, not_false_eq_true, IsUnit.mul_inv_cancel, one_mul]
      simp only [isUnit_iff_ne_zero, ne_eq, pow_eq_zero_iff', ZeroMemClass.coe_eq_zero,
        Units.ne_zero, false_and, not_false_eq_true, IsUnit.mul_inv_cancel]
      rfl
    inv_val := by
      simp only [map_inv₀, inv_pow, MulMemClass.mk_mul_mk, mul_assoc]
      simp only [← mul_assoc (u.1.1 ^ n1)⁻¹, isUnit_iff_ne_zero, ne_eq, map_eq_zero, ZeroMemClass.coe_eq_zero, Units.ne_zero, not_false_eq_true, IsUnit.mul_inv_cancel, one_mul]
      simp only [isUnit_iff_ne_zero, ne_eq, pow_eq_zero_iff', ZeroMemClass.coe_eq_zero,
        Units.ne_zero, false_and, not_false_eq_true, IsUnit.inv_mul_cancel, one_mul, map_eq_zero]
      rfl
  }
  apply DiscreteValuationRing.unit_mul_pow_congr_pow (p := πL) (q := πL) hirrL hirrL u2 u3 _ _
  simp only [← MulMemClass.coe_mul, ← SubmonoidClass.coe_pow] at hnu1
  apply Subtype.coe_inj.1 hnu1


  -- apply Uniformizer_pow_eq_of_associated hpiL
  -- let u3 : (vL.v.valuationSubring)ˣ := {
  --   val := ⟨(u.1.1 ^ n1) * (algebraMap M L u1.1.1) * u2.1.1⁻¹, by
  --     apply ValuationSubring.mul_mem
  --     · apply ValuationSubring.mul_mem
  --       · exact pow_mem u.1.2 n1
  --       · refine (mem_valuationSubring_iff v ((algebraMap M L) ↑↑u1)).mpr ?_
  --         refine (IsValExtension.val_map_le_one_iff u1.1.1).mpr ?_
  --         apply (mem_valuationSubring_iff v u1.1.1).1 u1.1.2
  --     · sorry
  --     ⟩
  --   inv := ⟨u2.1.1 * (algebraMap M L u1.1.1⁻¹) * (u.1.1⁻¹) ^ n1, sorry⟩
  --   val_inv := by sorry
  --   inv_val := by sorry
  -- }
  -- use u3
  -- simp only [u3]
  -- rw [← mul_assoc]
  -- --this might be simpler
  -- have h : ↑πL ^ (n1 * n) * ((↑↑u ^ n1) * (algebraMap M L) ↑↑u1) = ↑πL ^ n2 * u2.1.1 := by
  --   rw [hnu1, pow_mul, mul_pow]
  --   ring
  -- simp only [h, isUnit_iff_ne_zero, ne_eq, ZeroMemClass.coe_eq_zero, Units.ne_zero,
  --   not_false_eq_true, IsUnit.mul_inv_cancel_right]


open Polynomial Algebra

-- #synth CommMonoid (Multiplicative ℤ)
-- #check Valuation
-- --i_G/H σ = (1 / e_L/K) * ∑_{s → σ} i_G s
-- #check toAdd_prod
-- #check Valuation.map_mul
-- #check Valuation.map_eq_of_sub_lt

-- theorem exsit_preimage : ∃ s : (L ≃ₐ[K] L), (restrictNormalHom M) s = σ := by
--   apply AlgEquiv.restrictNormalHom_surjective

-- #check Subalgebra K L
-- #check AlgEquiv.restrictValuationSubring_apply
-- theorem adjoin_val_gen_eq_top (x : PowerBasis 𝒪[K] 𝒪[L]) : adjoin K {x.gen.1} = ⊤ := by
--   rw [adjoin_singleton_eq_range_aeval]
--   ext t
--   constructor <;> intro ht
--   · trivial
--   · cases' h : ValuationSubring.mem_or_inv_mem vL.v.valuationSubring t with h1 h1
--     · obtain ⟨f, hf⟩ := Algebra.exists_eq_aeval_generator (PowerBasis.adjoin_gen_eq_top x) (⟨t, h1⟩ : vL.v.valuationSubring)
--       use Polynomial.ofSubring 𝒪[K] f
--       simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
--       simp only [← Subtype.coe_inj] at hf
--       rw [hf]
--       rw [aeval_eq_sum_range, aeval_eq_sum_range]
--       have heq : (Polynomial.ofSubring 𝒪[K] f).natDegree = f.natDegree := by
--         simp only [Polynomial.ofSubring]
--         rw [Polynomial.natDegree_sum_eq_of_disjoint]
--         simp only [natDegree_monomial, ZeroMemClass.coe_eq_zero]
--         by_cases hc : f = 0
--         · simp only [hc, support_zero, coeff_zero, ↓reduceIte, Finset.sup_empty, bot_eq_zero',natDegree_zero]
--         · apply le_antisymm
--           · apply Finset.sup_le
--             intro b hb
--             by_cases hc : f.coeff b = 0
--             · simp only [hc, ↓reduceIte, zero_le]
--             · simp only [hc, ↓reduceIte]
--               exact le_natDegree_of_mem_supp b hb
--           · by_cases hc' : f.natDegree = 0
--             · rw [hc']
--               simp only [zero_le]
--             · apply (Finset.le_sup_iff _).2
--               use f.natDegree
--               constructor
--               · apply natDegree_mem_support_of_nonzero hc
--               · have hne : f.coeff f.natDegree ≠ 0 := mem_support_iff.mp (natDegree_mem_support_of_nonzero hc)
--                 simp only [hne, ↓reduceIte, le_refl]
--               rw [bot_eq_zero']
--               by_contra hcon
--               simp only [not_lt, nonpos_iff_eq_zero] at hcon
--               absurd hc'
--               exact hcon
--         simp only [mem_support_iff, ne_eq, monomial_eq_zero_iff, ZeroMemClass.coe_eq_zero, and_self]
--         intro a ha b hb hab
--         simp only [Set.mem_setOf_eq] at ha hb
--         simp only [ne_eq, Function.comp_apply, natDegree_monomial, ZeroMemClass.coe_eq_zero, ha, ↓reduceIte, hb]
--         exact hab
--       simp only [heq, AddSubmonoidClass.coe_finset_sum]
--       apply Finset.sum_congr rfl
--       intro i hi
--       rw [coeff_ofSubring]
--       rfl
--     · obtain ⟨f, hf⟩ := Algebra.exists_eq_aeval_generator (PowerBasis.adjoin_gen_eq_top x) (⟨t⁻¹, h1⟩ : vL.v.valuationSubring)


--       sorry

#help tactic cases

theorem aux_1 (σ : M ≃ₐ[K] M) (hσ : σ ≠ .refl) (x : PowerBasis 𝒪[K] 𝒪[L]) (y : PowerBasis 𝒪[K] 𝒪[M]) [Algebra.IsSeparable (LocalRing.ResidueField 𝒪[K]) (LocalRing.ResidueField 𝒪[L])] [Algebra.IsSeparable (LocalRing.ResidueField 𝒪[M]) (LocalRing.ResidueField 𝒪[L])] : (algebraMap M L) (σ ↑y.gen - ↑y.gen) ∣ (∏ x_1 ∈ (⇑(restrictNormalHom M (K₁ := L)) ⁻¹' {σ}).toFinset.attach, (x_1.1 x.gen - x.gen)) := by
  let a := (algebraMap M L) (σ ↑y.gen - ↑y.gen)
  let b := (∏ x_1 ∈ (⇑(restrictNormalHom M (K₁ := L)) ⁻¹' {σ}).toFinset.attach, (x_1.1 x.gen - x.gen))
  have hin : ∀ t : (L ≃ₐ[M] L), t x.gen ∈ 𝒪[L] := by
    intro t
    rw [← DecompositionGroup.restrictValuationSubring_apply']
    refine SetLike.coe_mem ((DecompositionGroup.restrictValuationSubring' ?h) x.gen)
    exact mem_decompositionGroup t
  let f := ∏ t ∈ (⊤ : Set (L ≃ₐ[M] L)).toFinset, (C (⟨t x.gen, hin t⟩ : 𝒪[L]) - X)
  obtain ⟨s, hs⟩ := AlgEquiv.restrictNormalHom_surjective L σ
  have hin' : ∀ t : 𝒪[L], s t ∈ 𝒪[L] := by
    intro t
    rw [← DecompositionGroup.restrictValuationSubring_apply']
    refine SetLike.coe_mem ((DecompositionGroup.restrictValuationSubring' ?h) t)
    exact mem_decompositionGroup s
  let e : 𝒪[L] →+* 𝒪[L] := {
      toFun := fun t => ⟨s t, hin' t⟩
      map_one' := by
        simp only [OneMemClass.coe_one, _root_.map_one]
        rfl
      map_mul' := by
        simp only [Subring.coe_mul, _root_.map_mul, MulMemClass.mk_mul_mk, implies_true]
      map_zero' := by
        simp only [ZeroMemClass.coe_zero, _root_.map_zero]
        rfl
      map_add' := by
        simp only [Subring.coe_add, _root_.map_add, AddMemClass.mk_add_mk, implies_true]
    }
  let sf := Polynomial.map e f
  let sf' := ∏ t ∈ (⊤ : Set (L ≃ₐ[K] L)).toFinset, (X - C ((s * t) x.gen))
  have hcoeff : ∀ i : ℕ, coeff sf i = s (coeff f i).1 := by
    intro i
    rw [Polynomial.coeff_map]
    simp only [f, Polynomial.map_prod, e]
    simp only [Polynomial.map_sub, map_X, map_C, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    -- rw [heq, Polynomial.map_prod]
    -- simp only [Polynomial.map_sub, map_X, map_C, RingHom.coe_coe]
  have : a ∣ b := by
    have ha : a = s (algebraMap M L y.gen) - (algebraMap M L y.gen) := by
      simp only [a]
      simp only [_root_.map_sub, sub_left_inj]
      rw [← hs]
      apply AlgEquiv.restrictNormal_commutes
    have hb : b = eval x.gen (sf - f) := by
      rw [eval_sub]
      have heq : eval x.gen f = 0 := by
        simp only [f, eval_prod, eval_sub, eval_X, eval_C]
        refine Finset.prod_eq_zero_iff.mpr ?_
        use .refl
        simp only [Set.top_eq_univ, Set.toFinset_univ, Finset.mem_univ, coe_refl, id_eq, sub_self, and_self]
      rw [heq, sub_zero]
      --this has be done
      simp only [b, sf, f]
      rw [Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C, mul_apply, Polynomial.eval_prod, eval_sub, eval_C, eval_X]
      sorry
    rw [ha, hb, ← eval_C (a := (s (algebraMap M L y.gen) - (algebraMap M L y.gen))) (x := x.gen.1), ← IsValExtension.coe_algebraMap_valuationSubring]
    use (eval (x.gen.1) (C (s ↑((algebraMap ↥𝒪[M] ↥𝒪[L]) y.gen) - ↑((algebraMap ↥𝒪[M] ↥𝒪[L]) y.gen))))⁻¹ * (eval x.gen (sf - f)).1
    rw [← mul_assoc]
    -- apply Polynomial.eval_dvd
    -- apply (Polynomial.C_dvd_iff_dvd_coeff _ _).2
    -- intro i
    -- rw [coeff_sub, hcoeff i]
    rw [mul_inv_cancel₀, one_mul]
    simp only [IsValExtension.coe_algebraMap_integer, _root_.map_sub, eval_sub, eval_C, ne_eq]
    by_contra hc
    absurd hσ
    have hs' : (s.restrictNormal M) = σ := hs
    simp only [sub_eq_zero, ← AlgEquiv.restrictNormal_commutes, hs'] at hc
    apply NoZeroSMulDivisors.algebraMap_injective M L at hc
    rw [eq_iff_ValuationSubring]
    apply PowerBasis.algHom_ext' y
    rw [← Subtype.val_inj, AlgEquiv.restrictValuationSubring_apply, AlgEquiv.restrictValuationSubring_apply, coe_refl, id_eq]
    exact hc
    -- have : (s.restrictNormal M) y.gen.1 = y.gen.1 := by
    --   have : Function.Injective (algebraMap M L) := by exact NoZeroSMulDivisors.algebraMap_injective M L
    --   apply this
    --   exact hc
      -- by_contra hc
      -- absurd hσ
      -- rw [sub_eq_zero] at hc
      -- rw [eq_iff_ValuationSubring]
      -- apply PowerBasis.algHom_ext' y
      -- rw [← Subtype.val_inj, AlgEquiv.restrictValuationSubring_apply, AlgEquiv.restrictValuationSubring_apply, coe_refl, id_eq]
      -- exact hc
    -- have hdvd : (algebraMap M L y.gen) ∣ f.coeff i := by
    --   use (algebraMap M L y.gen)⁻¹ * (f.coeff i)
    --   simp only [← mul_assoc]
    --   have : (algebraMap M L) ↑y.gen * ((algebraMap M L) ↑y.gen)⁻¹ = 1 := by
    --     refine mul_inv_cancel₀ ?_
    --     refine (map_ne_zero_iff (algebraMap M L) ?hf).mpr ?_
    --     exact NoZeroSMulDivisors.algebraMap_injective M L
    --     simp only [ne_eq, ZeroMemClass.coe_eq_zero]
    --     sorry
    --   rw [this, one_mul]
    -- obtain ⟨t, ht⟩ := hdvd
    -- have ht' : s (f.coeff i) = s ((algebraMap M L) y.gen) * t := by
    --   rw [ht]
    --   sorry
    -- use t
    -- nth_rw 2 [ht]
    -- rw [ht', sub_mul]
  sorry

instance : IsScalarTower 𝒪[K] 𝒪[M] 𝒪[L] where
  smul_assoc x y z := SetLike.coe_eq_coe.mp (IsScalarTower.smul_assoc x.1 y.1 z.1)

instance : NoZeroSMulDivisors 𝒪[M] 𝒪[L] :=  NoZeroSMulDivisors.iff_algebraMap_injective.mpr (IsValExtension.integerAlgebra_injective M L)

def i (s : L ≃ₐ[K] L) (hs : (restrictNormalHom M) s = σ) (a : { x // x ∈ ((restrictNormalHom (K₁ := L) M) ⁻¹' {σ}).toFinset }) (ha : a ∈ (⇑(restrictNormalHom M) ⁻¹' {σ}).toFinset.attach) : L ≃ₐ[M] L where
  toFun x := (s⁻¹ * a) x
  invFun x := (a.1⁻¹ * s) x
  left_inv := by
    simp only [mul_apply, Function.LeftInverse]
    intro x
    rw [← eq_symm_apply, ← eq_symm_apply]
    rfl
  right_inv := by
    simp only [mul_apply, Function.RightInverse, Function.LeftInverse]
    intro x
    rw [← eq_symm_apply, ← eq_symm_apply]
    rfl
  map_mul' x y := by
    simp only [mul_apply, _root_.map_mul]
  map_add' x y := by simp only [mul_apply, _root_.map_add]
  commutes' x := by
    rcases a with ⟨a, ha'⟩
    simp only [Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at ha'
    simp only [mul_apply]
    rw [← AlgEquiv.restrictNormal_commutes,  ← AlgEquiv.restrictNormal_commutes]
    have hs : s.restrictNormal M = σ := hs
    have ha' : a.restrictNormal M = σ := ha'
    have hinv : (s⁻¹.restrictNormal M) = (s.restrictNormal M)⁻¹ := by
      apply (restrictNormalHom M).map_inv
    rw [hinv, hs, ha']
    have hx : σ⁻¹ (σ x) = x := by
      rw [← eq_symm_apply]
      rfl
    rw [hx]

theorem AlgEquiv.restrictNormalHom_restrictScalarsHom {x : (L ≃ₐ[M] L)} : AlgEquiv.restrictNormalHom M (AlgEquiv.restrictScalarsHom K x) = 1 := by sorry

#check (restrictNormalHom M).map_inv
theorem aux10 (σ : M ≃ₐ[K] M) (s : L ≃ₐ[K] L) (hs : (restrictNormalHom M) s = σ) (x : PowerBasis 𝒪[K] 𝒪[L]) : ∏ x_1 ∈ (⇑(restrictNormalHom M) ⁻¹' {σ}).toFinset.attach, (x_1.1 x.gen.1 - x.gen.1) = ∏ x_1 ∈ (⊤ : Set (L ≃ₐ[M] L)).toFinset, (s (x_1 ↑x.gen) - ↑x.gen) := by
  apply Finset.prod_bij (i σ s hs)
  · intro a ha
    simp only [i, Set.top_eq_univ, Set.toFinset_univ, mul_apply, Finset.mem_univ]
  · intro a1 ha1 a2 ha2 ha
    simp only [i, mul_apply, AlgEquiv.mk.injEq, Equiv.mk.injEq] at ha
    rcases ha with ⟨ha1, ha2⟩
    ext x
    apply AlgEquiv.injective s⁻¹
    apply congr_fun ha1
  · intro b hb
    let a' : { x // x ∈ ((restrictNormalHom M (K₁ := L)) ⁻¹' {σ}).toFinset} := {
      val := s * ((restrictScalarsHom K) b)
      property := by
        simp only [Set.mem_toFinset, Set.mem_preimage, _root_.map_mul, Set.mem_singleton_iff, hs, AlgEquiv.restrictNormalHom_restrictScalarsHom, mul_one]
    }
    have ha : a' ∈ (⇑(restrictNormalHom M) ⁻¹' {σ}).toFinset.attach := Finset.mem_attach (⇑(restrictNormalHom M) ⁻¹' {σ}).toFinset a'
    use a'
    use ha
    simp only [i]
    simp only [inv_mul_cancel_left, mul_inv_rev, inv_mul_cancel_right]
    rfl
  · intro a ha
    simp only [i, mul_apply, AlgEquiv.coe_mk, Equiv.coe_fn_mk, sub_left_inj]
    rw [← eq_symm_apply, eq_symm_apply, ← symm_symm s, eq_symm_apply]
    rfl

theorem aux_12 (x : PowerBasis 𝒪[K] 𝒪[L]) : ∀ t : (L ≃ₐ[M] L), t x.gen ∈ 𝒪[L] := by
  intro t
  rw [mem_integer_iff, val_map_le_one_iff, ← mem_integer_iff]
  exact SetLike.coe_mem x.gen
  exact algEquiv_preserve_val_of_complete t


theorem aux_13 (x : PowerBasis 𝒪[K] 𝒪[L]) : ∀ t : (L ≃ₐ[M] L), ⟨t x.gen, aux_12 x t⟩ ∈ (minpoly (↥𝒪[M]) x.gen).aroots 𝒪[L] := by
  intro t
  simp only [mem_roots', ne_eq, IsRoot.def, eval_map_algebraMap]
  constructor
  · by_contra hc
    have h1 : minpoly 𝒪[M] x.gen = 0 := by
      apply_fun Polynomial.map (algebraMap ↥𝒪[M] ↥𝒪[L])
      simp only [Polynomial.map_zero]
      exact hc
      apply Polynomial.map_injective
      exact IsValExtension.integerAlgebra_injective M L
    have h2 : minpoly 𝒪[M] x.gen ≠ 0 := by
      apply minpoly.ne_zero
      exact IsIntegral.isIntegral x.gen
    exact h2 h1
  · have hmem : t ∈ decompositionGroup M L := mem_decompositionGroup t
    conv =>
      enter [1, 1, 1, 1]
      rw [← DecompositionGroup.restrictValuationSubring_apply' hmem]
    rw [SetLike.eta, aeval_algHom_apply]
    have hzero : ((aeval x.gen) (minpoly (↥𝒪[M]) x.gen)) = 0 := minpoly.aeval (↥𝒪[M]) x.gen
    rw [hzero]
    exact map_zero (DecompositionGroup.restrictValuationSubring' hmem)


def i1 (x : PowerBasis 𝒪[K] 𝒪[L]) (a : L ≃ₐ[M] L) (ha : a ∈ Finset.univ) : { y // y ∈ (minpoly (↥𝒪[M]) x.gen).aroots 𝒪[L]} := ⟨⟨a x.gen, aux_12 x a⟩, aux_13 x a⟩


def i2 (x : PowerBasis 𝒪[K] 𝒪[L]) (a : 𝒪[M]) (ha : a ∈ (minpoly (↥𝒪[M]) x.gen).roots) : 𝒪[L] := ⟨algebraMap 𝒪[M] 𝒪[L] a, SetLike.coe_mem ((algebraMap ↥𝒪[M] ↥𝒪[L]) a)⟩

theorem aux_14 (x :𝒪[L]) : (minpoly M x.1) = Polynomial.ofSubring 𝒪[M] (minpoly 𝒪[M] x) := by sorry

instance : Algebra.IsSeparable 𝒪[M] 𝒪[L] where
  isSeparable' := by
    intro x
    simp only [IsSeparable]

    sorry



#check minpoly.unique
#check Polynomial.monic_prod_of_monic
#check minpoly.algebraMap_eq
#check Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
#check PowerBasis.liftEquiv'
theorem aux_11 (x : PowerBasis 𝒪[K] 𝒪[L]) : Polynomial.map (algebraMap 𝒪[M] 𝒪[L]) (minpoly 𝒪[M] x.gen) = ∏ t ∈ (⊤ : Set (L ≃ₐ[M] L)).toFinset, (X - C (⟨t x.gen, aux_12 x t⟩ : 𝒪[L])) := by
  rw [← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (p := minpoly 𝒪[M] x.gen)]
  simp only [Polynomial.map_multiset_prod]
  simp only [Multiset.map_map, Function.comp_apply, Polynomial.map_sub, map_X, map_C]
  simp only [Set.top_eq_univ, Set.toFinset_univ]
  --rw [@Fintype.prod_equiv (S →ₐ[R] F) _ _ (PowerBasis.AlgHom.fintype pb) _ _ pb.liftEquiv'(fun σ => σ pb.gen) (fun x => x) ?_]
  have hprod : ∏ x_1 : L ≃ₐ[M] L, (X - C (⟨x_1 ↑x.gen, aux_12 x x_1⟩ : 𝒪[L])) = ∏ t : { y // y ∈ (minpoly 𝒪[M] x.gen).aroots 𝒪[L]}, (X - C t.1) := by
    apply Finset.prod_bij (i1 x)
    · intro a ha
      simp only [i1, Finset.mem_univ]
    · intro a1 ha1 a2 ha2 ha
      simp only [i1, Subtype.mk.injEq] at ha
      rw [eq_iff_ValuationSubring]
      apply_fun restrictScalars 𝒪[K]
      apply PowerBasis.algHom_ext' x
      rw [← AlgEquiv.restrictValuationSubring_apply, ← AlgEquiv.restrictValuationSubring_apply] at ha
      simp only [Subtype.val_inj] at ha
      simp only [restrictScalars_apply]
      exact ha
      exact restrictScalarsHom_injective ↥𝒪[K]
      -- apply PowerBasis.algHom_ext'
      -- rw [← Subtype.val_inj, AlgEquiv.restrictValuationSubring_apply, AlgEquiv.restrictValuationSubring_apply]
      -- exact ha
    · intro b hb
      simp only [i1]
      let a : L ≃ₐ[M] L := {
        toFun := by sorry
        invFun := sorry
        left_inv := sorry
        right_inv := sorry
        map_mul' := sorry
        map_add' := sorry
        commutes' := sorry
      }
      use a
      have ha : a ∈ Finset.univ := Finset.mem_univ a
      use ha

      sorry
    · intro a ha
      simp only [i1]
  rw [hprod, Finset.prod_mem_multiset _ _ (fun t => X - C t), Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr, Polynomial.aroots]
  have hmap : Multiset.map (fun x ↦ X - C ((algebraMap ↥𝒪[M] ↥𝒪[L]) x)) (minpoly (↥𝒪[M]) x.gen).roots = Multiset.map (fun x ↦ X - C x) (Polynomial.map (algebraMap ↥𝒪[M] ↥𝒪[L]) (minpoly (↥𝒪[M]) x.gen)).roots := by
    refine Multiset.map_eq_map_of_bij_of_nodup (fun x ↦ X - C ((algebraMap ↥𝒪[M] ↥𝒪[L]) x)) (fun x ↦ X - C x) ?_ ?_ (i2 x) ?_ ?_ ?_ ?_
    · refine nodup_roots ?refine_1.hsep
      apply Algebra.IsSeparable.isSeparable'
    · apply nodup_roots
      apply Polynomial.Separable.map
      apply Algebra.IsSeparable.isSeparable'
    · intro a ha
      simp only [i2]
      simp only [IsValExtension.coe_algebraMap_integer, mem_roots', ne_eq, IsRoot.def, eval_map_algebraMap]
      constructor
      · by_contra hc
        have h1 : minpoly 𝒪[M] x.gen = 0 := by
          apply_fun Polynomial.map (algebraMap ↥𝒪[M] ↥𝒪[L])
          simp only [Polynomial.map_zero]
          exact hc
          apply Polynomial.map_injective
          exact IsValExtension.integerAlgebra_injective M L
        have h2 : minpoly 𝒪[M] x.gen ≠ 0 := by
          apply minpoly.ne_zero
          exact IsIntegral.isIntegral x.gen
        exact h2 h1
      · simp only [← IsValExtension.coe_algebraMap_valuationSubring, SetLike.eta]
        apply (Polynomial.aeval_algebraMap_eq_zero_iff _ _ _).2
        apply (Polynomial.mem_roots_iff_aeval_eq_zero _).1 ha
        apply minpoly.ne_zero
        exact IsIntegral.isIntegral x.gen
    · intro a1 ha1 a2 ha2 ha
      simp only [i2, IsValExtension.coe_algebraMap_integer, Subtype.mk.injEq, algebraMap.coe_inj, SetLike.coe_eq_coe] at ha
      exact ha
    · intro b hb
      simp only [i2]
      -- obtain ⟨algMapinv, halg⟩ := Function.Injective.hasLeftInverse (NoZeroSMulDivisors.algebraMap_injective 𝒪[M] 𝒪[L])
      -- let a := algMapinv b
      -- use a
      -- have ha : a ∈ (minpoly (↥𝒪[M]) x.gen).roots := by sorry
      -- use ha
      -- simp only [a]
      -- simp only [IsValExtension.coe_algebraMap_integer]
      sorry
    · intro a ha
      simp only [i2]
  rw [hmap]
  · simp only [aroots]
    apply nodup_roots
    apply Polynomial.Separable.map
    apply Algebra.IsSeparable.isSeparable'
  · intro x
    rfl
  · refine minpoly.monic ?hp.hx
    exact IsIntegral.isIntegral x.gen
  ·
    sorry



theorem aux_2 (σ : M ≃ₐ[K] M) (x : PowerBasis 𝒪[K] 𝒪[L]) (y : PowerBasis 𝒪[K] 𝒪[M]) [Algebra.IsSeparable (LocalRing.ResidueField 𝒪[K]) (LocalRing.ResidueField 𝒪[L])] [Algebra.IsSeparable (LocalRing.ResidueField 𝒪[M]) (LocalRing.ResidueField 𝒪[L])] : (∏ x_1 ∈ (⇑(restrictNormalHom M (K₁ := L)) ⁻¹' {σ}).toFinset.attach, (x_1.1 x.gen - x.gen)) ∣ (algebraMap M L) (σ ↑y.gen - ↑y.gen):= by
  let a := (algebraMap M L) (σ ↑y.gen - ↑y.gen)
  let b := (∏ x_1 ∈ (⇑(restrictNormalHom M (K₁ := L)) ⁻¹' {σ}).toFinset.attach, (x_1.1 x.gen - x.gen))
  have hin : ∀ t : (L ≃ₐ[M] L), t x.gen ∈ 𝒪[L] := by
    intro t
    rw [← DecompositionGroup.restrictValuationSubring_apply']
    refine SetLike.coe_mem ((DecompositionGroup.restrictValuationSubring' ?h) x.gen)
    exact mem_decompositionGroup t
  let f := ∏ t ∈ (⊤ : Set (L ≃ₐ[M] L)).toFinset, (C (⟨t x.gen, hin t⟩ : 𝒪[L]) - X)
  obtain ⟨s, hs⟩ := AlgEquiv.restrictNormalHom_surjective L σ
  have hin' : ∀ t : 𝒪[L], s t ∈ 𝒪[L] := by
    intro t
    rw [← DecompositionGroup.restrictValuationSubring_apply']
    refine SetLike.coe_mem ((DecompositionGroup.restrictValuationSubring' ?h) t)
    exact mem_decompositionGroup s
  let e : 𝒪[L] →+* 𝒪[L] := {
      toFun := fun t => ⟨s t, hin' t⟩
      map_one' := by
        simp only [OneMemClass.coe_one, _root_.map_one]
        rfl
      map_mul' := by
        simp only [Subring.coe_mul, _root_.map_mul, MulMemClass.mk_mul_mk, implies_true]
      map_zero' := by
        simp only [ZeroMemClass.coe_zero, _root_.map_zero]
        rfl
      map_add' := by
        simp only [Subring.coe_add, _root_.map_add, AddMemClass.mk_add_mk, implies_true]
    }
  let sf := Polynomial.map e f
  let sf' := ∏ t ∈ (⊤ : Set (L ≃ₐ[K] L)).toFinset, (X - C ((s * t) x.gen))
  have : b ∣ a := by
    have hy : ∃ g : 𝒪[K][X], eval x.gen (Polynomial.map (algebraMap 𝒪[K] 𝒪[L]) g) = algebraMap 𝒪[M] 𝒪[L] y.gen := by
      obtain ⟨g, hg⟩ := Algebra.exists_eq_aeval_generator (PowerBasis.adjoin_gen_eq_top x) (algebraMap 𝒪[M] 𝒪[L] y.gen)
      use g
      rw [hg]
      simp only [eval_map_algebraMap]
    -- have hmin : f = Polynomial.map (algebraMap M L) (minpoly M x.gen.1) := by sorry
    obtain ⟨g, hg⟩ := hy
    let g_sub_y := Polynomial.map (algebraMap 𝒪[K] 𝒪[M]) g - C y.gen
    have ha : - a = eval x.gen (Polynomial.map e  (Polynomial.map (algebraMap 𝒪[M] 𝒪[L]) g_sub_y)) := by
      simp only [a, g_sub_y]
      have hg' : (Polynomial.map e (Polynomial.map (algebraMap 𝒪[M] 𝒪[L]) (Polynomial.map (algebraMap 𝒪[K] 𝒪[M]) g))) = (Polynomial.map (algebraMap 𝒪[K] 𝒪[L]) g) := by
        rw [Polynomial.map_map (algebraMap 𝒪[K] 𝒪[M]), ← (IsScalarTower.algebraMap_eq 𝒪[K] 𝒪[M] 𝒪[L])]
        ext n
        simp only [coeff_map, e, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, IsValExtension.coe_algebraMap_valuationSubring, AlgEquiv.commutes]
      simp only [_root_.map_sub, Polynomial.map_sub, map_C, hg', eval_sub, eval_map_algebraMap, eval_C, ← eval_map_algebraMap, hg, neg_sub, AddSubgroupClass.coe_sub, IsValExtension.coe_algebraMap_integer,sub_right_inj, e, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, IsValExtension.coe_algebraMap_integer, ← hs]
      apply AlgEquiv.restrictNormal_commutes
      -- simp only [a, g_sub_y]
      -- have hg' : (Polynomial.map e (Polynomial.map (algebraMap M L) (Polynomial.map (algebraMap K M) g))) = (Polynomial.map (algebraMap K L)  g) := by
      --   rw [Polynomial.map_map (algebraMap K M), ← (IsScalarTower.algebraMap_eq K M L)]
      --   ext n
      --   simp only [coeff_map, e]
      --   simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, AlgEquiv.commutes]
      -- simp only [_root_.map_sub, Polynomial.map_sub, map_C, hg', eval_sub, eval_map_algebraMap, eval_C]
      -- rw [← eval_map_algebraMap, hg]
      -- simp only [neg_sub, sub_right_inj, e]
      -- simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, ← hs]
      -- apply AlgEquiv.restrictNormal_commutes
    have hdvd : minpoly 𝒪[M] x.gen ∣ g_sub_y := by
      apply minpoly.isIntegrallyClosed_dvd
      exact IsIntegral.isIntegral x.gen
      simp only [g_sub_y, ← eval_map_algebraMap, Polynomial.map_sub, Polynomial.map_map (algebraMap 𝒪[K] 𝒪[M]) (algebraMap 𝒪[M] 𝒪[L]) g, ← (IsScalarTower.algebraMap_eq 𝒪[K] 𝒪[M] 𝒪[L]), eval_sub, hg, map_C, eval_C, sub_self]
      -- apply minpoly.dvd_iff.2
      -- simp only [g_sub_y]
      -- rw [← eval_map_algebraMap, Polynomial.map_sub, Polynomial.map_map (algebraMap K M) (algebraMap M L) g, ← (IsScalarTower.algebraMap_eq K M L), eval_sub, hg]
      -- simp only [map_C, eval_C, sub_self]
    obtain ⟨h, hh⟩ := hdvd
    have hb : b = eval x.gen sf := by
      simp only [b, sf, f]
      rw [Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C, mul_apply, Polynomial.eval_prod, eval_sub, eval_C, eval_X]
      simp only [ SubmonoidClass.coe_finset_prod,AddSubgroupClass.coe_sub, e]
      simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
      apply Finset.prod_bij
      --apply Finset.prod_bij
      repeat sorry
    have hmin : f = Polynomial.map (algebraMap 𝒪[M] 𝒪[L]) (minpoly 𝒪[M] x.gen) := by
      sorry
    rw [← dvd_neg, ha, hb]
    simp only [sf, hmin]
    use (eval x.gen (Polynomial.map e (Polynomial.map (algebraMap 𝒪[M] 𝒪[L]) h))).1
    simp only [← Subring.coe_mul, Subtype.coe_inj]
    simp only [← eval_mul, ← Polynomial.map_mul]
    exact congrArg (eval x.gen) (congrArg (Polynomial.map e) (congrArg (Polynomial.map (algebraMap ↥𝒪[M] ↥𝒪[L])) hh))

    -- apply eval_dvd
    -- simp only [map_dvd_map']

    -- rw [ha, hb]
    -- apply Polynomial.eval_dvd
    -- use Polynomial.map (algebraMap M L) h
    -- ext i
    -- simp only [coeff_map]

    -- have hmin : f = Polynomial.map (algebraMap M L) (minpoly M x.gen.1) := by sorry
    -- rw [← dvd_neg, ha, hb]
    -- simp only [sf, hmin]
    -- apply eval_dvd
    -- simp only [map_dvd_map']
    -- use h
  sorry


#check Polynomial.map
#check Polynomial.C_dvd_iff_dvd_coeff
#check Polynomial.eval_dvd
#check Polynomial.reverse
#check Polynomial.comp
theorem prop3
  (σ : M ≃ₐ[K] M) (x : PowerBasis 𝒪[K] 𝒪[L]) (y : PowerBasis 𝒪[K] 𝒪[M]) [Algebra.IsSeparable (LocalRing.ResidueField 𝒪[K]) (LocalRing.ResidueField 𝒪[L])] [Algebra.IsSeparable (LocalRing.ResidueField 𝒪[M]) (LocalRing.ResidueField 𝒪[L])] :
    ∑ s ∈ ((restrictNormalHom M)⁻¹' {σ}), i_[L/K] s
    = (ramificationIdx M L) * i_[M/K] σ := by
  by_cases hσ : σ = .refl
  · sorry
  -- · subst hσ
  --   rw [lowerIndex_refl, ENat.mul_top]
  --   · have : (.refl : L ≃ₐ[K] L) ∈ (restrictNormalHom M)⁻¹' {.refl} := by
  --       rw [Set.mem_preimage, Set.mem_singleton_iff, ← AlgEquiv.aut_one, ← AlgEquiv.aut_one,
  --         _root_.map_one]
  --     rw [WithTop.sum_eq_top]
  --     exact ⟨.refl, Set.mem_toFinset.mpr this, lowerIndex_refl⟩
  --   · intro h
  --     rw [← ENat.coe_zero, ← ENat.some_eq_coe, WithTop.coe_eq_coe] at h
  --     apply ramificationIdx_ne_zero M L h
  · simp only [lowerIndex_of_powerBasis y, lowerIndex_of_powerBasis x]
    simp only [hσ, ↓reduceDIte]
    -- let g : ((restrictNormalHom M (K₁ := L))⁻¹' {σ}) → ℕ∞ := fun t => (-Multiplicative.toAdd (WithZero.unzero (val_map_powerBasis_sub_ne_zero x (preimage_nerefl σ hσ t.1 t.2)))).toNat
    rw [← Finset.sum_attach]
    conv =>
      enter [1, 2]
      ext t
      simp only [preimage_nerefl σ hσ t.1 (Set.mem_toFinset.1 t.2), ↓reduceDIte]
    rw [← ENat.coe_mul, ← Nat.cast_sum]
    apply Nat.cast_inj.2
    rw [← Nat.cast_inj (R := ℤ), Nat.cast_sum]
    conv =>
      enter [1, 2]
      ext t
      rw [Int.toNat_of_nonneg (val_mappb_sub_self_toAdd_nonpos (preimage_nerefl σ hσ t.1 (Set.mem_toFinset.mp t.2)) x), ← toAdd_inv]
    conv_rhs =>
        rw [Nat.cast_mul, Int.toNat_of_nonneg (val_mappb_sub_self_toAdd_nonpos hσ y), mul_comm, ← toAdd_inv, ← Int.toAdd_pow, inv_pow]
    rw [← toAdd_prod]
    apply Equiv.congr_arg
    rw [Finset.prod_inv_distrib, inv_inj, ← WithZero.coe_inj, WithZero.coe_pow, WithZero.coe_unzero, WithZero.coe_prod]
    have hy1 : (σ y.gen - y.gen) ∈ vM.v.valuationSubring := by sorry
      -- apply sub_mem
      -- · apply (mem_valuationSubring_iff v (σ ↑y.gen)).mpr
      --   rw [val_map_le_one_iff]
      --   exact SetLike.coe_mem y.gen
      --   exact algEquiv_preserve_val_of_complete σ
      -- · exact SetLike.coe_mem y.gen
    have hy2 : (⟨σ y.gen - y.gen, hy1⟩ : vM.v.valuationSubring) ≠ 0 := by sorry
      -- apply Subtype.coe_ne_coe.1
      -- simp only [ZeroMemClass.coe_zero]
      -- by_contra hc
      -- absurd hσ
      -- rw [sub_eq_zero] at hc
      -- rw [eq_iff_ValuationSubring]
      -- apply PowerBasis.algHom_ext' y
      -- rw [← Subtype.val_inj, AlgEquiv.restrictValuationSubring_apply, AlgEquiv.restrictValuationSubring_apply, coe_refl, id_eq]
      -- exact hc
    simp only [WithZero.coe_unzero, Valuation.prolongs_by_ramificationIndex hy1 hy2, ← _root_.map_prod]
    obtain ⟨π, hpi⟩ := exists_Uniformizer_ofDiscrete vL.v
    let a := (algebraMap M L) (σ ↑y.gen - ↑y.gen)
    let b := (∏ x_1 ∈ (⇑(restrictNormalHom M (K₁ := L)) ⁻¹' {σ}).toFinset.attach, (x_1.1 x.gen - x.gen))
    have hr1 : a ∈ v.valuationSubring := by sorry
    --   simp only [a]
    --   refine (mem_valuationSubring_iff v ((algebraMap M L) (σ ↑y.gen - ↑y.gen))).mpr ?_
    --   simp only [IsValExtension.val_map_le_one_iff]
    --   apply (mem_valuationSubring_iff v ((σ ↑y.gen - ↑y.gen))).mp
    --   exact hy1
    have hr1' :  (⟨a, hr1⟩ : vL.v.valuationSubring) ≠ 0 := by sorry
      -- apply Subtype.coe_ne_coe.1
      -- simp only [ZeroMemClass.coe_zero, a]
      -- apply (_root_.map_ne_zero (algebraMap M L)).mpr
      -- apply Subtype.coe_ne_coe.2 at hy2
      -- simp only [ZeroMemClass.coe_zero] at hy2
      -- exact hy2
    have hr2 : b ∈ v.valuationSubring := by sorry
      -- simp only [b, mem_valuationSubring_iff, map_prod]
      -- apply Finset.prod_le_one
      -- exact fun i a ↦ WithZero.zero_le (v (i.1 ↑x.gen - ↑x.gen))
      -- intro i hi
      -- exact val_map_sub_le_one (mem_decompositionGroup i.1) x.gen
    have hr2' :  (⟨b, hr2⟩ : vL.v.valuationSubring) ≠ 0 := by sorry
      -- apply Subtype.coe_ne_coe.1
      -- simp only [ZeroMemClass.coe_zero, b]
      -- apply Finset.prod_ne_zero_iff.2
      -- intro ⟨i, hi⟩ hi1
      -- by_contra hc
      -- nth_rw 2 [← id_eq x.gen] at hc
      -- rw [sub_eq_zero, ← coe_refl (R := 𝒪[K])] at hc
      -- have heq : i = .refl := by
      --   rw [eq_iff_ValuationSubring]
      --   apply PowerBasis.algHom_ext' x
      --   rw [← Subtype.val_inj, AlgEquiv.restrictValuationSubring_apply, AlgEquiv.restrictValuationSubring_apply]
      --   exact hc
      -- simp only [Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hi
      -- absurd hσ
      -- rw [← hi, heq]
      -- apply (restrictNormalHom M).map_one
    obtain ⟨n1, u1, hnu1⟩ := pow_Uniformizer vL.v (r := ⟨a, hr1⟩) hr1' ⟨π, hpi⟩
    obtain ⟨n2, u2, hnu2⟩ := pow_Uniformizer vL.v (r := ⟨b, hr2⟩) hr2' ⟨π, hpi⟩
    simp only [_root_.map_sub, SubmonoidClass.coe_pow, a, b] at hnu1 hnu2
    simp only [_root_.map_sub, hnu1, hnu2, _root_.map_mul, _root_.map_pow, val_valuationSubring_unit, mul_one]
    apply congrArg
    obtain ⟨s, hs⟩ := AlgEquiv.restrictNormalHom_surjective L σ
    let f := ∏ t ∈ (⊤ : Set (L ≃ₐ[K] L)).toFinset, (X - C (t x.gen))
    let e : L →+* L := {
      toFun := fun t => s t
      map_one' := map_one s
      map_mul' := AlgEquiv.map_mul' s
      map_zero' := map_zero s
      map_add' := AlgEquiv.map_add' s
    }
    let sf := Polynomial.map e f
    let sf' := ∏ t ∈ (⊤ : Set (L ≃ₐ[K] L)).toFinset, (X - C ((s * t) x.gen))
    have hcoeff : ∀ i : ℕ, coeff sf i = s (coeff f i) := by sorry
      -- intro i
      -- simp only [sf, e, coeff_map, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    apply le_antisymm
    · have hab : b ∣ a := by
        have hy : ∃ g : K[X], eval x.gen.1 (Polynomial.map (algebraMap K L) g) = algebraMap M L y.gen := by
          have hgen : adjoin K {x.gen.1} = ⊤ := by sorry
          obtain ⟨g, hg⟩ := Algebra.exists_eq_aeval_generator hgen (algebraMap M L y.gen)
          sorry
        -- have hmin : f = Polynomial.map (algebraMap M L) (minpoly M x.gen.1) := by sorry
        obtain ⟨g, hg⟩ := hy
        let g_sub_y := Polynomial.map (algebraMap K M) g - C y.gen.1
        have hdvd : minpoly M x.gen.1 ∣ g_sub_y := by
          apply minpoly.dvd_iff.2
          simp only [g_sub_y]
          sorry
        obtain ⟨h, hh⟩ := hdvd
        have ha : a = eval x.gen.1 (Polynomial.map e (Polynomial.map (algebraMap M L) g_sub_y)) := by sorry
        have hb : b = eval x.gen.1 sf := by sorry
        rw [ha, hb]
        apply Polynomial.eval_dvd
        use Polynomial.map (algebraMap M L) h
        ext i
        simp only [coeff_map]
        sorry
      simp only [a, b, _root_.map_sub, hnu1, hnu2] at hab
      obtain ⟨t, ht⟩ := hab
      have hr : t ∈ v.valuationSubring := by sorry
      have hr' :  (⟨t, hr⟩ : vL.v.valuationSubring) ≠ 0 := by sorry
      obtain ⟨n, u, hnu⟩ := pow_Uniformizer vL.v hr' ⟨π, hpi⟩
      have hn : n2 + n = n1 := by sorry
      rw [← hn]
      linarith
    · have hab : a ∣ b := by
        --simp only [a, b]
        have ha : a = s (algebraMap M L y.gen) - (algebraMap M L y.gen) := by sorry
        have hb : b = eval x.gen.1 (sf - f) := by sorry
        rw [ha, hb, ← eval_C (a := (s (algebraMap M L y.gen) - (algebraMap M L y.gen))) (x := x.gen.1)]
        apply Polynomial.eval_dvd
        apply (Polynomial.C_dvd_iff_dvd_coeff _ _).2
        intro i
        rw [coeff_sub, hcoeff i]
        have hdvd : (algebraMap M L y.gen) ∣ f.coeff i := by sorry
        obtain ⟨t, ht⟩ := hdvd
        have ht' : s (f.coeff i) = s ((algebraMap M L) y.gen) * t := by sorry
        use t
        nth_rw 2 [ht]
        rw [ht', sub_mul]
      simp only [a, b, _root_.map_sub, hnu1, hnu2] at hab
      obtain ⟨t, ht⟩ := hab

      sorry
    -- have : ∑ x : ((restrictNormalHom M)⁻¹' {σ}), g x = ↑(ramificationIdx M L) * ↑(-Multiplicative.toAdd (WithZero.unzero (val_map_powerBasis_sub_ne_zero y (of_eq_false (eq_false hσ))))).toNat := by
    --   unfold g
    --   rw [← ENat.coe_mul, ← Nat.cast_sum]
    --   apply Nat.cast_inj.mpr ?_
    --   rw [← Nat.cast_inj (R := ℤ)]
    --   have h1 : 0 ≤ -Multiplicative.toAdd (WithZero.unzero (val_map_powerBasis_sub_ne_zero y (of_eq_false (eq_false hσ)))) := by sorry
    --   have h2 : ∀ t : ((restrictNormalHom M)⁻¹' {σ}), 0 ≤ -Multiplicative.toAdd (WithZero.unzero (val_map_powerBasis_sub_ne_zero x (preimage_nerefl σ hσ t.1 t.2))) := by sorry
    --   conv =>
    --     right
    --     rw [Nat.cast_mul, Int.toNat_of_nonneg h1, mul_comm, ← toAdd_inv, ← Int.toAdd_pow, inv_pow, toAdd_inv]
    --   rw [Nat.cast_sum]
    --   conv =>
    --     enter [1, 2]
    --     ext t
    --     rw [Int.toNat_of_nonneg (h2 t)]
    --   #check Finset.sum_attach_univ
    --   #check Finset.attach ((restrictNormalHom M) ⁻¹' {σ}).toFinset
    --   sorry

#help tactic conv

    /- Need:
    2. all valuations are discrete
    3. 𝒪[L] / 𝒪[M] admits a power basis b, so that the minpoly of b over M has coeff in 𝒪[M]
    -/


end sum_lowerIndex

section aux

variable {K K' L : Type*} {ΓK : outParam Type*} [Field K] [Field K'] [Field L] [vK' : Valued K' ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK'.v] [IsDiscrete vL.v] [Algebra K L] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L] [IsValExtension K' L] [Normal K K'] [Normal K L] [FiniteDimensional K L] [FiniteDimensional K K']
