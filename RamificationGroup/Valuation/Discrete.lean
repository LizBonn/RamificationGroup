/-
# WARNING : `WithZero.lean` uses `sorry`
-/

import LocalClassFieldTheory.DiscreteValuationRing.Complete
import LocalClassFieldTheory.DiscreteValuationRing.DiscreteNorm
import RamificationGroup.ForMathlib.Henselian
import RamificationGroup.Valued.Defs
import LocalClassFieldTheory.ForMathlib.RankOneValuation

open Valuation Valued DiscreteValuation Multiplicative

theorem Int.eq_neg_one_of_dvd_neg_one {x : ℤ} (h : x ≤ 0) (h' : x ∣ -1) : x = -1 := by
  let y := -x
  simp only [show x = -y by rw [neg_neg], Left.neg_nonpos_iff, reduceNeg, dvd_neg, neg_dvd, neg_inj] at *
  exact Int.eq_one_of_dvd_one h h'

namespace WithZero

theorem ofAdd_eq_neg_one_of_pow_eq_neg_one {x : ℤₘ₀} (h1 : x ≤ 1) {n : ℤ} (hn : x ^ n = ofAdd (-1 : ℤ)) : x = ofAdd (-1 : ℤ) := by
  by_cases hn0 : n = 0
  · simp only [hn0, zpow_zero, Int.reduceNeg, ofAdd_neg, coe_inv, one_eq_inv] at hn
    contradiction
  · match x with
    | 0 =>
      simp only [zero_le', Int.reduceNeg, ofAdd_neg, coe_inv, zero_eq_inv, zero_ne_coe] at *
      rw [zero_zpow _ hn0] at hn
      contradiction
    | .coe (.ofAdd a)  =>
      change ((ofAdd (n * a) : Multiplicative ℤ) : ℤₘ₀) = (ofAdd (-1 : ℤ)) at hn
      change ↑(ofAdd a) ≤ (((ofAdd (0 : ℤ)): Multiplicative ℤ) : ℤₘ₀) at h1
      rw [coe_le_coe, Multiplicative.ofAdd_le] at h1
      rw [coe_inj] at *
      show a = -1
      change n * a = -1 at hn
      apply Int.eq_neg_one_of_dvd_neg_one h1 (dvd_of_mul_left_eq _ hn)

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
  | .ofNat a => simp only [Int.ofNat_eq_coe, zpow_natCast, _root_.map_pow]
  | .negSucc a => simp only [zpow_negSucc, map_inv₀, _root_.map_pow]

end division_ring

section field

variable {K : Type*} [Field K] {ΓK ΓK': outParam Type*}
  [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓK']
  {v : Valuation K ΓK} {v' : Valuation K ΓK'}

#check ValuationSubring.valuation_eq_one_iff
#check Valuation.isEquiv_valuation_valuationSubring

theorem val_valuationSubring_unit {u : v.valuationSubringˣ} :
  v u = 1 := by
  rw [(isEquiv_iff_val_eq_one v v.valuationSubring.valuation).mp (isEquiv_valuation_valuationSubring v), ValuationSubring.valuation_unit]

theorem isUnit_in_valuationSubring_of_val_eq_one {x : K} (h : v x = 1) :
  IsUnit (⟨x, le_of_eq h⟩ : v.valuationSubring) := by
  rw [ValuationSubring.valuation_eq_one_iff, ← (isEquiv_iff_val_eq_one v v.valuationSubring.valuation).mp (isEquiv_valuation_valuationSubring v), h]

/-- create a term of `v.valuationSubringˣ` from a term `x : K` with `v x = 1`-/
noncomputable def unitOfValOne {x : K} (h : v x = 1) : v.valuationSubringˣ :=
  (isUnit_in_valuationSubring_of_val_eq_one h).choose

theorem unitOfValOne_elem {x : K} (h : v x = 1) : (unitOfValOne h).1 = x := by
  unfold unitOfValOne
  rw [(isUnit_in_valuationSubring_of_val_eq_one h).choose_spec]

theorem val_unitOfValOne_eq_one {x : K} (h : v x = 1) : v (unitOfValOne h).1 = 1 := by
  rw [unitOfValOne_elem]
  exact h

end field

end Valuation

namespace DiscreteValuation

variable {K : Type*} [Field K]
  {v v' : Valuation K ℤₘ₀} [IsDiscrete v] [IsDiscrete v']

theorem pow_Uniformizer_all {x : K} (hx : x ≠ 0) (π : Uniformizer v) :
  ∃ n : ℤ, ∃ u : v.valuationSubringˣ, x = (π.1 : K) ^ n  * u.1 := by
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
    simp only [SubmonoidClass.coe_pow, zpow_neg, zpow_natCast, inv_inv, mul_eq_mul_left_iff, pow_eq_zero_iff', ZeroMemClass.coe_eq_zero, ne_eq]
    left; rw [← inv_eq_iff_eq_inv]
    field_simp; symm
    calc
      _ = (((1 /ₚ u) * u : Valuation.valuationSubring v) : K) := by congr
      _ = (1 : K) := by simp only [one_divp, Units.inv_mul, OneMemClass.coe_one]

theorem pow_Uniformizer' {x : K} (h0 : x ≠ 0) (hx : v x ≤ 1) (π : Uniformizer v) :
  ∃ n : ℕ, ∃ u : v.valuationSubring ˣ, x = (π.1 : K) ^ n * u.1 := by
  let r : v.valuationSubring := ⟨x, hx⟩
  have : r ≠ 0 := by simp only [ne_eq, Subtype.ext_iff, ZeroMemClass.coe_zero, h0, not_false_eq_true]
  rcases pow_Uniformizer v this π with ⟨n, u, hnu⟩
  use n, u
  rw [show x = r.1 by rfl, hnu, SubmonoidClass.coe_pow]

#check Valuation.unit_map_eq
theorem val_pow_Uniformizer {π : Uniformizer v} {n : ℕ} {u : v.valuationSubringˣ} :
  v ((π.1 : K) ^ n * u.1) = ofAdd (-n : ℤ) := by
  rw [v.map_mul, Valuation.map_pow, π.2, val_valuationSubring_unit, mul_one, ← WithZero.coe_pow]
  congr 1
  simp only [Int.reduceNeg, ofAdd_neg, inv_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one]

theorem val_pow_Uniformizer_all {π : Uniformizer v} {n : ℤ} {u : v.valuationSubringˣ} :
  v ((π.1 : K) ^ n * u.1) = ofAdd (-n : ℤ) := by
  rw [v.map_mul, Valuation.map_zpow, π.2, val_valuationSubring_unit, mul_one, ← WithZero.coe_zpow]
  congr 1
  change n * -1 = -n
  exact mul_neg_one n

theorem val_pow_Uniformizer_all' {π : K} (hπ : IsUniformizer v π) {n : ℤ} {u : v.valuationSubringˣ} :
  v (π ^ n * u.1) = ofAdd (-n : ℤ) := by
  let ϖ := Uniformizer.mk' _ _ hπ
  rw [show π = ϖ.1 by exact rfl, val_pow_Uniformizer_all]

/--If `π : K` is a uniformizer for `v`, and `v x ≤ 1 → v' x ≤ 1, ∀ x : K`, then `π` is also a uniformizer for `v'`.-/
lemma isUniformizer_of_uniformizer_of_le_one_le_one (h : ∀{x : K}, v x ≤ 1 → v' x ≤ 1)
  (π : Uniformizer v) : IsUniformizer v' π.1 := by
  rcases exists_Uniformizer_ofDiscrete v' with ⟨π', hπ'⟩
  rcases pow_Uniformizer_all (Uniformizer_ne_zero v' hπ') π with ⟨m, u, hmu⟩
  replace hmu := congrArg v' hmu
  rw [_root_.map_mul, map_zpow₀,
    eq_one_of_eq_one_of_le_one_le_one h val_valuationSubring_unit, mul_one, hπ'] at hmu
  rw [IsUniformizer, WithZero.ofAdd_eq_neg_one_of_pow_eq_neg_one (h <| le_of_lt <| Uniformizer_valuation_lt_one v π.2) hmu.symm]

/--If `π : K` is a uniformizer for `v`, and `v` is equivalent to `v'`, then `π` is also a uniformizer for `v'`.-/
theorem isUniformizer_of_uniformizer_of_equiv (h : v.IsEquiv v')
  (π : Uniformizer v) : IsUniformizer v' π.1 := isUniformizer_of_uniformizer_of_le_one_le_one
  (fun {_} hx ↦ ((isEquiv_iff_val_le_one v v').mp h).mp hx) π

theorem val_pow_Uniformizer_all_of_equiv (h : v.IsEquiv v') {π : Uniformizer v} {n : ℤ} {u : v.valuationSubringˣ} :
  v' ((π.1 : K) ^ n * u.1) = ofAdd (-n : ℤ) := by
  rw [v'.map_mul, Valuation.map_zpow,
    isUniformizer_of_uniformizer_of_equiv h]
  have : v' (u : K) = 1 := by
    rw [← (isEquiv_iff_val_eq_one _ _).mp h, val_valuationSubring_unit]
  simp only [Int.reduceNeg, ofAdd_neg, WithZero.coe_inv, inv_zpow', zpow_neg, this, mul_one, inv_inj,
    ← WithZero.coe_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one] -- `WithZero.coe_zpow` should be tagged with @[norm_cast], but it is not.

theorem lt_one_lt_one_of_le_one_le_one (h : ∀{x : K}, v x ≤ 1 → v' x ≤ 1) {x : K} (hx : v x < 1) : v' x < 1 := by
  by_cases xne0 : x = 0
  · simp only [xne0, _root_.map_zero, zero_lt_one]
  rcases exists_Uniformizer_ofDiscrete v with ⟨π, hπ⟩
  rcases pow_Uniformizer' xne0 (le_of_lt hx) ⟨π, hπ⟩ with ⟨n, u, hnu⟩
  have ngt1 : ((ofAdd (-n) : Multiplicative ℤ) : ℤₘ₀) < 1 := by
    apply congrArg v at hnu
    rw [val_pow_Uniformizer] at hnu
    rw [← hnu]
    exact hx
  simp only at hnu
  have : v' u.1 = 1 := eq_one_of_eq_one_of_le_one_le_one h val_valuationSubring_unit
  rw [show (u.1 : K) = (unitOfValOne this).1 by rw [unitOfValOne_elem]] at hnu
  let π' : Uniformizer v' := Uniformizer.mk' v' _ (isUniformizer_of_uniformizer_of_le_one_le_one h ⟨π, hπ⟩)
  have : π.1 = π'.1 := by simp only [Uniformizer.mk', π']
  rw [this] at hnu
  apply congrArg v' at hnu
  rw [hnu, val_pow_Uniformizer]
  exact ngt1

/-- Two discrete valuations `v` and `v'` on a field `K` are equivalent, if `v x ≤ 1 → v' x ≤ 1, ∀x : K`. -/
theorem isEquiv_of_le_one_le_one (h : ∀{x : K}, v x ≤ 1 → v' x ≤ 1) :
  v.IsEquiv v' := by
  apply isEquiv_of_val_le_one
  refine fun {x} ↦ ⟨h, ?_⟩
  by_cases xne0 : x = 0
  · simp only [xne0, _root_.map_zero, zero_le', forall_true_left]
  intro v'xle
  by_contra! vxgt
  have : v' x⁻¹ < 1 := lt_one_lt_one_of_le_one_le_one h <| (one_lt_val_iff _ xne0).mp vxgt
  have : (1 : ℤₘ₀) < 1 := by
    nth_rw 1 [← Valuation.map_one v']
    rw [show (1 : K) = x * x⁻¹ by simp only [ne_eq, xne0, not_false_eq_true, mul_inv_cancel], Valuation.map_mul, show (1 : ℤₘ₀) = 1 * 1 by rfl]
    apply mul_lt_mul_of_lt_of_le₀ v'xle (by simp only [ne_eq, one_ne_zero, not_false_eq_true]) this
  contradiction

/-- For discrete valuations, being equivalent is the same as being equal. -/
theorem isEquiv_iff_eq : v.IsEquiv v' ↔ v = v' := by
  constructor
  · intro heq; ext x
    by_cases h0 : x = 0
    · simp only [h0, _root_.map_zero]
    · rcases exists_Uniformizer_ofDiscrete v with ⟨π, hπ⟩
      rcases pow_Uniformizer_all h0 ⟨π, hπ⟩ with ⟨n, u, hnu⟩
      rw [hnu, val_pow_Uniformizer_all, val_pow_Uniformizer_all_of_equiv heq]
  · exact IsEquiv.of_eq

end DiscreteValuation

section nontrivial

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

section non_field

variable {R : Type*} [Ring R]

namespace Valuation

class Nontrivial (v : Valuation R Γ) : Prop where
  nontrivial : ∃ r : R, v r ≠ 0 ∧ v r ≠ 1

@[deprecated]
theorem nontrivial_def (v : Valuation R Γ) [Nontrivial v] : ∃ r : R, v r ≠ 0 ∧ v r ≠ 1 := Nontrivial.nontrivial

instance instNontrivialToRankOne (v : Valuation R Γ) [RankOne v] : v.Nontrivial where
  nontrivial := RankOne.nontrivial v

end Valuation

end non_field

section field

variable {R : Type*} [Field R]

namespace DiscreteValuation

theorem valuationSubring_DVR_of_equiv_discrete {v u : Valuation R ℤₘ₀} [IsDiscrete u]
  (h : v.IsEquiv u) : DiscreteValuationRing v.valuationSubring := by
  rw [(Valuation.isEquiv_iff_valuationSubring _ _).mp h]
  infer_instance

def ofNontrivial (v : Valuation R ℤₘ₀) [Nontrivial v] : Valuation R ℤₘ₀ := sorry

variable (v : Valuation R ℤₘ₀) [Nontrivial v]

theorem isEquiv_ofNontrivial : v.IsEquiv (ofNontrivial v) := by sorry

#check DiscreteValuationRing

instance : IsDiscrete (ofNontrivial v) := by sorry

instance : DiscreteValuationRing v.valuationSubring :=
  valuationSubring_DVR_of_equiv_discrete (isEquiv_ofNontrivial v)

end DiscreteValuation

end field

end nontrivial

end approximation

section adic_complete

variable {K : Type*} [Field K] [vK : Valued K ℤₘ₀]

local notation "m[" K "]" => LocalRing.maximalIdeal 𝒪[K]

variable [CompleteSpace K] [IsDiscrete vK.v]

variable (K)

-- theorem isHausdorff_of_complete_of_discrete [CompleteSpace K] [IsDiscrete vK.v] : IsHausdorff m[K] 𝒪[K] where
--   haus' := by
--     sorry

-- instance instIsAdicCompleteToCompleteToDiscrete [CompleteSpace K] [IsDiscrete vK.v] : IsAdicComplete (LocalRing.maximalIdeal 𝒪[K]) 𝒪[K] := by
--   sorry

-- #synth HenselianLocalRing vK.valuationSubring

end adic_complete
