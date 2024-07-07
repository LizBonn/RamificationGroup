import RamificationGroup.Valued.Hom.Lift
import RamificationGroup.Valuation.Extension
import RamificationGroup.ForMathlib.Algebra.Algebra.Tower
import Mathlib.FieldTheory.Galois
import LocalClassFieldTheory.LocalField.Basic
import RamificationGroup.ForMathlib.Algebra.Algebra.PowerBasis
import RamificationGroup.Valued.Hom.ValExtension'

/-
# Lower Numbering Ramification Group

## Main Definitions

## Main Theorem

## TODO

prove theorems using Bichang's preparation in section SeparatedExhausive

rename theorems, many theorem should be named as LowerRamificationGroup.xxx, not lowerRamificationGroup_xxx

-/

open DiscreteValuation Valued Valuation

-- <-1 decomposition group
-- >= -1 decompositiongroup and v (s x - x) ≤ 1
section def_lower_rami_grp

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [vS : Valued S ℤₘ₀] [Algebra R S]

-- variable (K L : Type*) {ΓL : outParam Type*} [Field K] [Field L] [LinearOrderedCommGroupWithZero ΓL] [vL : Valued L ℤₘ₀] [Algebra K L]

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
        simp
      _ ≤ _ := hs.2 ⟨s⁻¹ a, (val_map_le_one_iff (f := (s.symm : S →+* S))
        (Valuation.IsEquiv_comap_symm hs.1) a.1).mpr a.2⟩

scoped [Valued] notation:max " G(" S:max "/" R:max ")_[" u:max "] " => lowerRamificationGroup R S u

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
    simp only [WithZero.coe_le_coe, div_le_iff_le_mul, div_mul_cancel, inv_le_inv_iff,
      Multiplicative.ofAdd_le]
    exact hab

end def_lower_rami_grp

section autCongr

variable {R S S': Type*} {ΓR : outParam Type*} [CommRing R] [Ring S] [Ring S'] [vS : Valued S ℤₘ₀] [vS : Valued S' ℤₘ₀] [Algebra R S] [Algebra R S']

theorem autCongr_mem_lowerRamificationGroup_iff {f : S ≃ₐ[R] S'} (hf : ∀ a : S, v a = v (f a)) (s : S ≃ₐ[R] S) (u : ℤ) : s ∈ G(S/R)_[u] ↔ (AlgEquiv.autCongr f s : S' ≃ₐ[R] S') ∈ G(S'/R)_[u] := by
  simp only [lowerRamificationGroup, ofAdd_sub, ofAdd_neg, Subtype.forall, Subgroup.mem_mk,
    Set.mem_setOf_eq, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply]
  constructor <;>
  intro h <;>
  constructor <;>
  intro a ha
  · sorry -- need theorem/def of lift of f to integer is isom
  · sorry
  · sorry
  · sorry

end autCongr

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

-- noncomputable instance : ConditionallyCompleteLinearOrderBot ℤₘ₀ := inferInstanceAs (ConditionallyCompleteLinearOrderBot (WithZero ℤ))

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

end lowerIndex

section ScalarTower

variable {R : Type*} {R' S: Type*} {ΓR ΓS ΓA ΓB : outParam Type*} [CommRing R] [CommRing R'] [Ring S]
[vS : Valued S ℤₘ₀]
[Algebra R S] [Algebra R R'] [Algebra R' S] [IsScalarTower R R' S]

/-- `This should be add to correct place` -/
instance {R Γ₀: Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀): Nonempty v.integer := by
  use (0 : R)
  change v 0 ≤ 1
  simp only [_root_.map_zero, zero_le']

instance {K Γ₀: Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] [vK : Valued K Γ₀]: Nonempty 𝒪[K] := inferInstanceAs (Nonempty vK.v.integer)

@[simp]
theorem lowerIndex_refl : (i_[S/R] .refl) = ⊤ := by
  simp only [AlgEquiv.lowerIndex, AlgEquiv.coe_refl, id_eq, sub_self, _root_.map_zero, ciSup_const,
    ↓reduceDite]

@[simp]
theorem truncatedLowerIndex_refl (u : ℚ) : AlgEquiv.truncatedLowerIndex R S u .refl = u := by
  simp only [AlgEquiv.truncatedLowerIndex, lowerIndex_refl, ↓reduceDite]

section lowerIndex_inequality

variable {K K' L : Type*} {ΓK ΓK' : outParam Type*} [CommRing K] [Field K'] [Field L] [LinearOrderedCommGroupWithZero ΓK]
[LinearOrderedCommGroupWithZero ΓK'] [vL : Valued L ℤₘ₀] [Algebra K L]
[Algebra K K'] [Algebra K' L] [IsScalarTower K K' L]

/-- `h` should be `𝒪[L] is finite over 𝒪[K]`-/
theorem lowerIndex_ne_refl_of_FG (h : sorry) {s : L ≃ₐ[K] L} (hs : s ≠ .refl) : i_[L/K] s ≠ ⊤ := by
  intro heq
  simp only [AlgEquiv.lowerIndex, AddSubgroupClass.coe_sub,
    dite_eq_left_iff, ENat.coe_ne_top, imp_false, not_not] at heq
  have : ∀ x : vL.v.integer, v (s x - x) = 0 := by
    intro x
    apply le_of_eq at heq
    rw [show (0 : ℤₘ₀) = ⊥ by rfl, eq_bot_iff]
    refine (ciSup_le_iff' ?_).mp heq x -- this sorry is should be filled with bounded by one
    use 1
    intro a ha
    rcases ha with ⟨y, hy⟩
    rw [← hy, ← Valuation.mem_integer_iff]
    apply Subring.sub_mem
    sorry; sorry
  apply hs
  ext x
  rw [AlgEquiv.coe_refl, id_eq, ← sub_eq_zero, ← Valuation.zero_iff vL.v]
  rcases ValuationSubring.mem_or_inv_mem 𝒪[L] x with h | h
  · sorry
  · sorry

theorem lowerIndex_ne_one {s : decompositionGroup K L} (hs : s ≠ 1) : i_[L/K] s ≠ ⊤ := by
  intro heq
  simp only [AlgEquiv.lowerIndex, AddSubgroupClass.coe_sub,
    dite_eq_left_iff, ENat.coe_ne_top, imp_false, not_not] at heq
  have hL : ∀ x : vL.v.integer, s.1 x = x := by
    intro x
    apply le_of_eq at heq
    rw [← sub_eq_zero, ← Valuation.zero_iff vL.v, show (0 : ℤₘ₀) = ⊥ by rfl, eq_bot_iff]
    refine (ciSup_le_iff' ?_).mp heq x
    use 1
    intro a ha
    rcases ha with ⟨y, hy⟩
    rw [← hy, ← Valuation.mem_integer_iff]
    apply Subring.sub_mem
    · rw [mem_integer_iff, val_map_le_one_iff s.2]
      exact y.2
    · exact y.2 -- should have be proved somewhere else?
  apply hs
  ext x
  rw [decompositionGroup_one, AlgEquiv.coe_refl, id_eq]
  rcases ValuationSubring.mem_or_inv_mem 𝒪[L] x with h | h
  · exact hL ⟨x, h⟩
  · calc
    _ = (s.1 x⁻¹)⁻¹ := by simp only [inv_inv, map_inv₀]
    _ = _ := by rw [hL ⟨x⁻¹, h⟩, inv_inv]

@[simp]
theorem lowerIndex_eq_top_iff_eq_refl {s : decompositionGroup K L} : i_[L/K] s = ⊤ ↔ s = 1 := by
  constructor <;> intro h
  · contrapose! h
    apply lowerIndex_ne_one h
  · simp only [AlgEquiv.lowerIndex, h, OneMemClass.coe_one, AlgEquiv.one_apply, sub_self,
    _root_.map_zero, ciSup_const, ↓reduceDite]

--the type of `n` should be changed
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

end lowerIndex_inequality

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
variable (K L : Type*) [Field K] [Field L] [vK : Valued K ℤₘ₀] [IsDiscrete vK.v] [vL : Valued L ℤₘ₀] [Algebra K L] [IsValExtension K L] [FiniteDimensional K L]

section algebra_instances

/-- The conditions might be too strong.
The proof is almost the SAME with `Valuation.mem_integer_of_mem_integral_closure`. -/
instance instIsIntegrallyClosedToValuationSubring : IsIntegrallyClosed 𝒪[K] := by
  rw [isIntegrallyClosed_iff K]
  intro x ⟨p, hp⟩
  by_cases xne0 : x = 0
  · subst xne0; use 0; simp only [ValuationSubring.algebraMap_def, _root_.map_zero]
  by_cases vxgt1 : v x ≤ 1
  · use ⟨x, vxgt1⟩; rfl
  · exfalso
    push_neg at vxgt1
    letI : Invertible x := invertibleOfNonzero xne0
    have : v (aeval x⁻¹ (p.reverse - 1)) < 1 := by
      apply aeval_valuationSubring_lt_one_of_lt_one_self
      · simp only [coeff_sub, coeff_zero_reverse, hp.1, Monic.leadingCoeff, coeff_one_zero, sub_self]
      · apply (one_lt_val_iff v xne0).mp vxgt1
    apply ne_of_lt this
    have : aeval x⁻¹ (p.reverse - 1) = -1 := by
      rw [← add_neg_eq_zero]
      ring_nf
      simp only [_root_.map_add, _root_.map_neg, _root_.map_one, add_neg_cancel_left]
      rw [← invOf_eq_inv x, aeval_def, Polynomial.eval₂_reverse_eq_zero_iff, hp.2]
    rw [this, Valuation.map_neg, Valuation.map_one]

attribute [local instance 1001] Algebra.toSMul

instance : IsScalarTower 𝒪[K] 𝒪[L] L := inferInstanceAs (IsScalarTower vK.v.integer vL.v.integer L)

#check IsIntegralClosure.of_isIntegrallyClosed

instance [CompleteSpace K]: Algebra.IsIntegral 𝒪[K] 𝒪[L] where
  isIntegral := by
    intro ⟨x, hx⟩
    rw [show 𝒪[L] = valuationSubring vL.v by rfl,
      (Valuation.isEquiv_iff_valuationSubring _ _).mp
        (extension_valuation_equiv_extendedValuation_of_discrete (IsValExtension.val_isEquiv_comap (R := K) (A := L))),
      ← ValuationSubring.mem_toSubring, ← Extension.integralClosure_eq_integer, Subalgebra.mem_toSubring] at hx
    rcases hx with ⟨p, hp⟩
    refine ⟨p, hp.1, ?_⟩
    ext
    rw [show (0 : 𝒪[L]).val = 0 by rfl, ← hp.2,
      show algebraMap (vK.v.valuationSubring) L = algebraMap 𝒪[K] L by rfl]
    calc
      _ = 𝒪[L].subtype (eval₂ (algebraMap 𝒪[K] 𝒪[L]) ⟨x, hx⟩ p) := rfl
      _ = _ := by
        rw [Polynomial.hom_eval₂]
        simp only [ValuationSubring.algebraMap_def]
        congr

instance instIsIntegralClosureToValuationSubring [CompleteSpace K] : IsIntegralClosure 𝒪[L] 𝒪[K] L := by
  apply IsIntegralClosure.of_isIntegrallyClosed 𝒪[L] 𝒪[K] L


/-- Can't be inferred within 20000 heartbeats. -/
instance instIsNoetherianToValuationSubring : IsNoetherianRing 𝒪[K] := PrincipalIdealRing.isNoetherianRing

instance instNoethertianToValuationSubringExtension [CompleteSpace K] [IsSeparable K L] : IsNoetherian 𝒪[K] 𝒪[L] :=
  IsIntegralClosure.isNoetherian 𝒪[K] K L 𝒪[L]

noncomputable def PowerBasisValExtension [CompleteSpace K] [IsSeparable K L] [IsSeparable (LocalRing.ResidueField 𝒪[K]) (LocalRing.ResidueField 𝒪[L])] : PowerBasis 𝒪[K] 𝒪[L] :=
  letI : Nontrivial vL.v := nontrivial_of_valExtension K L
  PowerBasisExtDVR (integerAlgebra_injective K L)

end algebra_instances

variable {K L}
variable [CompleteSpace K]

theorem AlgEquiv.val_map_powerBasis_sub_ne_zero (pb : PowerBasis 𝒪[K] 𝒪[L]) {s : L ≃ₐ[K] L} (hs : s ≠ .refl) : vL.v (s pb.gen - pb.gen) ≠ 0 := by
  by_contra h
  rw [zero_iff, sub_eq_zero] at h
  apply hs
  rw [AlgEquiv.eq_iff_ValuationSubring]
  apply PowerBasis.algEquiv_ext pb
  ext; simp only [AlgEquiv.restrictValuationSubring_apply, h, AlgEquiv.coe_refl, id_eq]

open Polynomial in
theorem AlgEquiv.val_map_sub_le_powerBasis (pb : PowerBasis 𝒪[K] 𝒪[L]) (s : L ≃ₐ[K] L) (x : 𝒪[L]) : vL.v (s x - x) ≤ vL.v (s pb.gen - pb.gen) := by
  by_cases hs : s = .refl
  · subst hs
    simp only [AlgEquiv.coe_refl, id_eq, sub_self, _root_.map_zero, le_refl]
  rcases PowerBasis.exists_eq_aeval' pb x with ⟨f, hf⟩
  subst hf
  rcases taylor_order_zero_apply_aeval f pb.gen ((AlgEquiv.restrictValuationSubring s) pb.gen - pb.gen) with ⟨b, hb⟩
  rw [add_sub_cancel, add_comm, ← sub_eq_iff_eq_add, aeval_algHom_apply, Subtype.ext_iff] at hb
  simp only [AddSubgroupClass.coe_sub, AlgEquiv.restrictValuationSubring_apply, Submonoid.coe_mul, Subsemiring.coe_toSubmonoid, Subring.coe_toSubsemiring] at hb
  rw [hb, Valuation.map_mul]
  nth_rw 2 [← mul_one (v (s ↑pb.gen - ↑pb.gen))]
  rw [mul_le_mul_left₀]
  · exact b.2
  · apply AlgEquiv.val_map_powerBasis_sub_ne_zero pb hs

theorem AlgEquiv.iSup_val_map_sub_eq_powerBasis (pb : PowerBasis 𝒪[K] 𝒪[L]) (s : L ≃ₐ[K] L) :
  ⨆ x : vL.v.integer, v (s x - x) = v (s pb.gen - pb.gen) := by
  apply le_antisymm
  · apply ciSup_le <| AlgEquiv.val_map_sub_le_powerBasis pb s
  · apply le_ciSup (f := fun (x : 𝒪[L]) ↦ v (s x - x)) _ pb.gen
    use v (s pb.gen - pb.gen)
    intro y hy
    simp only [Set.mem_range, Subtype.exists, exists_prop] at hy
    rcases hy with ⟨a, ha⟩
    rw [← ha.2, show s a - a = s (⟨a, ha.1⟩ : 𝒪[L]) - (⟨a, ha.1⟩ : 𝒪[L]) by rfl]
    apply AlgEquiv.val_map_sub_le_powerBasis

open Classical in
/-- Should I `open Classical`? -/
theorem lowerIndex_of_powerBasis (pb : PowerBasis 𝒪[K] 𝒪[L]) (s : L ≃ₐ[K] L) :
  i_[L/K] s = if h : s = .refl then (⊤ : ℕ∞)
    else (- Multiplicative.toAdd (WithZero.unzero (AlgEquiv.val_map_powerBasis_sub_ne_zero pb h))).toNat := by
  by_cases h : s = .refl
  · simp only [h, lowerIndex_refl, ↓reduceDite]
  · unfold AlgEquiv.lowerIndex
    simp only [h, AlgEquiv.iSup_val_map_sub_eq_powerBasis pb, AlgEquiv.val_map_powerBasis_sub_ne_zero pb h, ↓reduceDite]

#synth Fintype (L ≃ₐ[K] L)

theorem lowerIndex_ne_refl {s : L ≃ₐ[K] L} (hs : s ≠ .refl) : i_[L/K] s ≠ ⊤ := by
  have : s ∈ decompositionGroup K L := by
    rw [decompositionGroup_eq_top]
    exact Subgroup.mem_top s
  rw [show s = (⟨s, this⟩ : decompositionGroup K L).1 by rfl]
  apply lowerIndex_ne_one
  intro h
  rw [Subtype.ext_iff, decompositionGroup_one] at h
  exact hs h

variable (K L) in
theorem aux1 : ⨆ s : {s : (L ≃ₐ[K] L) // s ≠ .refl}, i_[L/K] s ≠ ⊤ := by
  rw [← lt_top_iff_ne_top, iSup_lt_iff]
  sorry

#check le_truncatedLowerIndex_sub_one_iff_mem_lowerRamificationGroup
theorem aux0 {pb : PowerBasis 𝒪[K] 𝒪[L]}
  {u : ℕ} (hu : u > ⨆ s : {s : (L ≃ₐ[K] L) // s ≠ .refl}, i_[L/K] s)
  {s : L ≃ₐ[K] L} (hs : s ∈ G(L/K)_[u]) : s = .refl := by
  sorry


-- this uses local fields and bichang's work, check if the condition is too strong..., It should be O_L is finitely generated over O_K
theorem exist_lowerRamificationGroup_eq_bot [LocalField K] [LocalField L] : ∃ u : ℤ, G(L/K)_[u] = ⊥ := by
  use (WithTop.untop _ (aux1 K L) : ℕ) + 1
  sorry

end eq_bot

end ExhausiveSeperated

section aux

variable {K K' L : Type*} {ΓK : outParam Type*} [Field K] [Field K'] [Field L] [vK' : Valued K' ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK'.v] [IsDiscrete vL.v] [Algebra K L] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L] [IsValExtension K' L] [Normal K K'] [Normal K L] [FiniteDimensional K L] [FiniteDimensional K K']
