/-
# WARNING : `WithZero.lean` uses `sorry`
-/

import LocalClassFieldTheory.DiscreteValuationRing.Complete
import LocalClassFieldTheory.DiscreteValuationRing.DiscreteNorm
import RamificationGroup.ForMathlib.Henselian
import RamificationGroup.Valued.Defs



open Valuation Valued DiscreteValuation Multiplicative

#check IsRankOne
#check IsDiscrete
#check DiscreteValuation.isRankOne

#check Int.eq_one_of_dvd_one

theorem Int.eq_neg_one_of_dvd_neg_one {x : ℤ} (h : x ≤ 0) (h' : x ∣ -1) : x = -1 := by
  let y := -x
  simp only [show x = -y by rw [neg_neg], Left.neg_nonpos_iff, reduceNeg, dvd_neg, neg_dvd, neg_inj] at *
  exact Int.eq_one_of_dvd_one h h'


#check dvd_neg
#check Int.eq_one_of_dvd_one
#check ℤₘ₀
namespace WithZero

#check congrArg
#check ofAdd_eq_one
#check unzero
#check WithZero.coe_inj

#synth GroupWithZero ℤₘ₀


theorem ofAdd_eq_neg_one_of_pow_eq_neg_one {x : ℤₘ₀} (h1 : x ≤ 1) {n : ℤ} (hn : x ^ n = ofAdd (-1 : ℤ)) : x = ofAdd (-1 : ℤ) := by
  by_cases hn0 : n = 0
  · simp only [hn0, zpow_zero, Int.reduceNeg, ofAdd_neg, coe_inv, one_eq_inv] at hn
    contradiction
  · match x with
    | 0 =>
      simp at *
      rw [zero_zpow _ hn0] at hn
      contradiction
    | .coe (.ofAdd a)  =>
      change ((ofAdd (n * a) : Multiplicative ℤ) : ℤₘ₀) = (ofAdd (-1 : ℤ)) at hn
      change ↑(ofAdd a) ≤ (((ofAdd (0:ℤ)): Multiplicative ℤ) : ℤₘ₀) at h1
      rw [coe_le_coe, Multiplicative.ofAdd_le] at h1
      rw [coe_inj] at *
      show a = -1
      change n * a = -1 at hn
      apply Int.eq_neg_one_of_dvd_neg_one h1 (dvd_of_mul_left_eq _ hn)

/-
  have nne0 : n ≠ 0 := by
    intro a
    simp only [a, zpow_zero, Int.reduceNeg, ofAdd_neg, coe_inv, one_eq_inv] at hn
    rw [show (1 : ℤₘ₀) = ((1 : Multiplicative ℤ) : ℤₘ₀) by rfl, coe_inj] at hn
    have : ofAdd (1 : ℤ) ≠ (1 : Multiplicative ℤ) := by
      simp only [ne_eq, ofAdd_eq_one, one_ne_zero, not_false_eq_true]
    exact this hn
  have xne0 : x ≠ 0 := by
    intro a
    rw [a, zero_zpow n nne0] at hn
    revert hn
    simp only [Int.reduceNeg, ofAdd_neg, coe_inv, zero_eq_inv, zero_ne_coe, IsEmpty.forall_iff]
  rw [← coe_unzero xne0, ← coe_zpow, coe_inj] at hn
  rw [← coe_unzero xne0, coe_inj]
  rw [show (1 : ℤₘ₀) = ofAdd (0 : ℤ) by rfl] at h1
  rw [← coe_unzero xne0, coe_le_coe] at h1
  have : unzero xne0 = ofAdd (toAdd (unzero xne0)) := (ofAdd_toAdd _).symm
  rw [this, Multiplicative.ofAdd_le] at h1
  rw [this, ← ofAdd_zsmul] at hn
  replace hn := ofAdd_inj hn
  simp only [smul_eq_mul, Int.reduceNeg] at hn
  rw [this]
  congr 1
  apply Int.eq_neg_one_of_dvd_neg_one h1 (dvd_of_mul_left_eq _ hn)
-/

end WithZero
section approximation

namespace Valuation

section division_ring

variable {K : Type*} [DivisionRing K] {ΓK ΓK': outParam Type*}
  [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓK']
  {v : Valuation K ΓK} {v' : Valuation K ΓK'}

lemma eq_one_of_eq_one_of_le_one_le_one (h : ∀{x : K}, v x ≤ 1 → v' x ≤ 1) {u : K} (hu : v u = 1) : v' u = 1 := by
  apply le_antisymm
  · apply h <| le_of_eq hu
  · have : v' u ≠ 0 := by
      rw [Valuation.ne_zero_iff, ← Valuation.ne_zero_iff v, hu]
      exact one_ne_zero
    rw [← inv_le_one₀ this, ← map_inv₀]
    apply h <| le_of_eq _
    rw [map_inv₀, hu, inv_one]

variable (v) in
theorem map_zpow (x : K) (n : ℤ) :
  v (x ^ n) = v x ^ n := by
  match n with
  | .ofNat a => simp only [Int.ofNat_eq_coe, zpow_coe_nat, _root_.map_pow]
  | .negSucc a => simp only [zpow_negSucc, map_inv₀, _root_.map_pow]

end division_ring

section field

variable {K : Type*} [Field K] {ΓK ΓK': outParam Type*}
  [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓK']
  {v : Valuation K ΓK} {v' : Valuation K ΓK'}

#check ValuationSubring.valuation_eq_one_iff
#check Valuation.isEquiv_valuation_valuationSubring

theorem val_valuationSubring_unit {u : v.valuationSubringˣ} : v u = 1 := by
  rw [(isEquiv_iff_val_eq_one v v.valuationSubring.valuation).mp (isEquiv_valuation_valuationSubring v), ValuationSubring.valuation_unit]

theorem isUnit_in_valuationSubring_of_val_eq_one {x : K} (h : v x = 1) : IsUnit (⟨x, le_of_eq h⟩ : v.valuationSubring) := by
  rw [ValuationSubring.valuation_eq_one_iff, ← (isEquiv_iff_val_eq_one v v.valuationSubring.valuation).mp (isEquiv_valuation_valuationSubring v), h]

/-- create a term of `v.valuationSubringˣ` from a term `x : K` with `v x = 1`-/
noncomputable def UnitOfValOne {x : K} (h : v x = 1) : v.valuationSubringˣ :=
  (isUnit_in_valuationSubring_of_val_eq_one h).choose

theorem UnitOfValOne_elem {x : K} (h : v x = 1) : (UnitOfValOne h).1 = x := by
  unfold UnitOfValOne
  rw [(isUnit_in_valuationSubring_of_val_eq_one h).choose_spec]

theorem val_UnitOfValOne_eq_one {x : K} (h : v x = 1) : v (UnitOfValOne h).1 = 1 := by
  rw [UnitOfValOne_elem]
  exact h

#check ValuationSubring.mem_unitGroup_iff

end field

end Valuation

namespace DiscreteValuation

open IsRankOne
open scoped NNReal

variable {K : Type*} [Field K]
  {v v' : Valuation K ℤₘ₀} [IsDiscrete v] [IsDiscrete v']

theorem pow_Uniformizer_all {x : K} (hx : x ≠ 0) (π : Uniformizer v) :
  ∃ n : ℤ, ∃ u : v.valuationSubring ˣ, x = (π.1 : K) ^ n  * u.1 := by
  rcases ValuationSubring.mem_or_inv_mem v.valuationSubring x with h | h
  · let r : v.valuationSubring := ⟨x, h⟩
    have : r ≠ 0 := by simp only [ne_eq, Subtype.ext_iff, ZeroMemClass.coe_zero, hx, not_false_eq_true]
    rcases pow_Uniformizer v this π with ⟨n, u, hnu⟩
    use n, u
    rw [show x = r.1 by rfl, hnu]
    simp only [SubmonoidClass.coe_pow, zpow_coe_nat]
  · let r : v.valuationSubring := ⟨x⁻¹, h⟩
    have : r ≠ 0 := by simp only [ne_eq, Subtype.ext_iff, ZeroMemClass.coe_zero, inv_eq_zero, hx, not_false_eq_true]
    rcases pow_Uniformizer v this π with ⟨n, u, hnu⟩
    use -n, u⁻¹
    rw [← inv_inj, show x⁻¹ = r.1 by rfl, hnu, mul_inv]
    simp only [SubmonoidClass.coe_pow, zpow_neg, zpow_coe_nat, inv_inv, mul_eq_mul_left_iff, pow_eq_zero_iff', ZeroMemClass.coe_eq_zero, ne_eq]
    left; rw [← inv_eq_iff_eq_inv]
    field_simp; symm
    calc
      _ = (((1 /ₚ u) * u : Valuation.valuationSubring v) : K) := by congr
      _ = (1 : K) := by simp only [one_divp, Units.inv_mul, OneMemClass.coe_one]

theorem pow_Uniformizer' {x : K} (h0 : x ≠ 0) (hx : v x ≤ 1) (π : Uniformizer v) :
  ∃ n : ℕ, ∃ u : v.valuationSubring ˣ, x = (π.1 : K) ^ n  * u.1 := by
  let r : v.valuationSubring := ⟨x, hx⟩
  have : r ≠ 0 := by simp only [ne_eq, Subtype.ext_iff, ZeroMemClass.coe_zero, h0, not_false_eq_true]
  rcases pow_Uniformizer v this π with ⟨n, u, hnu⟩
  use n, u
  rw [show x = r.1 by rfl, hnu, SubmonoidClass.coe_pow]

#check Valuation.unit_map_eq
theorem val_pow_Uniformizer {π : Uniformizer v} {n : ℕ} {u : v.valuationSubringˣ} :
  v ((π.1 : K) ^ n * u.1) = Multiplicative.ofAdd (-n : ℤ) := by
  rw [v.map_mul, Valuation.map_pow, π.2, val_valuationSubring_unit, mul_one, ← WithZero.coe_pow]
  congr 1
  simp only [Int.reduceNeg, ofAdd_neg, inv_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one]

-- TODO: `map_zpow` for `ℤ`-pow
theorem val_pow_Uniformizer_all {π : Uniformizer v} {n : ℤ} {u : v.valuationSubringˣ} : v ((π.1 : K) ^ n * u.1) = Multiplicative.ofAdd (-n : ℤ) := by
  rw [v.map_mul, Valuation.map_zpow, π.2, val_valuationSubring_unit, mul_one, ← WithZero.coe_zpow]
  congr 1
  change n * -1 = -n
  exact mul_neg_one n

/--If `π : K` is a uniformizer for `v`, and `v x ≤ 1 → v' x ≤ 1 ∀x : K`, then `π` is also a uniformizer for `v'`.-/
lemma isUniformizer_of_uniformizer_of_le_one_le_one (h : ∀{x : K}, v x ≤ 1 → v' x ≤ 1) (π : Uniformizer v) : IsUniformizer v' π.1 := by
  rcases exists_Uniformizer_ofDiscrete v' with ⟨π', hπ'⟩
  rcases pow_Uniformizer_all (Uniformizer_ne_zero v' hπ') π with ⟨m, u, hmu⟩
  replace hmu := congrArg v' hmu
  rw [_root_.map_mul, map_zpow₀,
    eq_one_of_eq_one_of_le_one_le_one h val_valuationSubring_unit, mul_one, hπ'] at hmu
  rw [IsUniformizer, WithZero.ofAdd_eq_neg_one_of_pow_eq_neg_one (h <| le_of_lt <| Uniformizer_valuation_lt_one v π.2) hmu.symm]

/-- Two discrete valuations `v` and `v'` on a field `K` are equivalent, if `v x ≤ 1 → v' x ≤ 1, ∀x : K`. -/
theorem isEquiv_of_le_one_le_one (h : ∀{x : K}, v x ≤ 1 → v' x ≤ 1) :
  v.IsEquiv v' := by
  apply isEquiv_of_val_le_one
  refine fun {x} ↦ ⟨h, ?_⟩
  by_cases xne0 : x = 0
  · intro
    rw [xne0, Valuation.map_zero]
    exact zero_le_one
  intro v'xle
  -- rcases exists_Uniformizer_ofDiscrete v' with ⟨π, hπ⟩
  -- rcases pow_Uniformizer' xne0 v'xle ⟨π, hπ⟩ with ⟨n, u, hnu⟩
  -- simp only [SubmonoidClass.coe_pow] at hnu
  -- rw [hnu]

  sorry

theorem isEquiv_iff_eq : v.IsEquiv v' ↔ v = v' := by
  constructor
  ·
    sorry
  · exact IsEquiv.of_eq


end DiscreteValuation

end approximation


section adic_complete

variable {K : Type*} [Field K] [vK : Valued K ℤₘ₀]

local notation "m[" K "]" => LocalRing.maximalIdeal 𝒪[K]

variable [CompleteSpace K] [IsDiscrete vK.v]

variable (K)

theorem isHausdorff_of_complete_of_discrete [CompleteSpace K] [IsDiscrete vK.v] : IsHausdorff m[K] 𝒪[K] where
  haus' := by
    sorry

instance instIsAdicCompleteToCompleteToDiscrete [CompleteSpace K] [IsDiscrete vK.v] : IsAdicComplete (LocalRing.maximalIdeal 𝒪[K]) 𝒪[K] := by
  sorry

instance instHenselianLocalRingToCompleteToDiscrete :
  HenselianLocalRing vK.valuationSubring := inferInstance

end adic_complete
