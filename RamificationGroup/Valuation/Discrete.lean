import LocalClassFieldTheory.DiscreteValuationRing.Complete
import LocalClassFieldTheory.DiscreteValuationRing.DiscreteNorm
import RamificationGroup.ForMathlib.Henselian
import RamificationGroup.Valued.Hom.Defs



open Valuation Valued DiscreteValuation Multiplicative

#check IsRankOne
#check IsDiscrete
#check DiscreteValuation.isRankOne

#check ℤₘ₀

theorem WithZero.ofAdd_eq_neg_one_of_pow_eq_neg_one {x : ℤₘ₀} (h1 : x ≤ 1) {n : ℤ} (hn : x ^ n = ofAdd (-1 : ℤ)) : x = ofAdd (-1 : ℤ) := by
  sorry

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

-- TODO: `map_pow` for `ℤ`-pow
theorem val_pow_Uniformizer_all {π : Uniformizer v} {n : ℤ} {u : v.valuationSubringˣ} : v ((π.1 : K) ^ n * u.1) = Multiplicative.ofAdd (-n : ℤ) := by
  sorry

lemma isUniformizer_of_uniformizer_of_le_one_le_one (h : ∀{x : K}, v x ≤ 1 → v' x ≤ 1) (π : Uniformizer v) : IsUniformizer v' π.1 := by
  rcases exists_Uniformizer_ofDiscrete v' with ⟨π', hπ'⟩
  rcases pow_Uniformizer_all (Uniformizer_ne_zero v' hπ') π with ⟨m, u, hmu⟩
  replace hmu := congrArg v' hmu
  rw [_root_.map_mul, map_zpow₀,
    eq_one_of_eq_one_of_le_one_le_one h (val_valuationSubring_unit (u := u)), mul_one, hπ'] at hmu
  -- have : v' π.1 = ofAdd (-1 : ℤ) := by
  --   apply WithZero.ofAdd_eq_neg_one_of_pow_eq_neg_one _ (h <| le_of_lt <| Uniformizer_valuation_lt_one v π.2) hmu.symm
  --   rw [Valuation.ne_zero_iff]
  --   exact Uniformizer_ne_zero' v π
  rw [IsUniformizer, WithZero.ofAdd_eq_neg_one_of_pow_eq_neg_one (h <| le_of_lt <| Uniformizer_valuation_lt_one v π.2) hmu.symm]

/-- Two discrete valuations `v` and `v'` on a field `K` are equivalent, if `v x ≤ 1 → v' x ≤ 1, ∀x : K`. -/
theorem isEquiv_of_le_one_le_one (h : ∀{x : K}, v x ≤ 1 → v' x ≤ 1) :
  v.IsEquiv v' := by
  apply isEquiv_of_val_le_one
  refine fun {x} ↦ ⟨h, ?_⟩
  by_cases xne0 : x = 0
  · intro
    rw [show v x = 0 by rw[xne0, Valuation.map_zero]]
    exact zero_le_one
  intro v'xle
  rcases exists_Uniformizer_ofDiscrete v' with ⟨π, hπ⟩
  rcases pow_Uniformizer' xne0 v'xle ⟨π, hπ⟩ with ⟨n, u, hnu⟩
  simp only [SubmonoidClass.coe_pow] at hnu
  rw [hnu]



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
