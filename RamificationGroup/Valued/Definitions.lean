import RamificationGroup.Valuation.Integer
import Mathlib.Topology.Algebra.Valuation
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Topology.Order.Basic


instance {R : Type*} {Γ : outParam Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ] [Valued R Γ]: Preorder R := Preorder.lift Valued.v

open DiscreteValuation

section DiscretelyValued

class DiscretelyValued (R : Type*) [Ring R] extends Valued R ℤₘ₀ where
  is_discrete : (v.toFun).Surjective
  /- This `v_is_surj` is the same as Maria and Phillip's is_discrete -/
  -- exist_val_one : ∃ x : R, Valued.v x = ofInt 1
  /- Is this definition OK? Wait for the theorems to decide -/
  /- This is different but includes Nm0 case-/

class CompleteDiscretelyValued (R : Type*) [Ring R] extends DiscretelyValued R, CompleteSpace R

end DiscretelyValued


section DVF

namespace Valued
-- this def is the same as `Valuation.integer`, it only serves for notation `𝒪[K]`
abbrev integer (K : Type*) [DivisionRing K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] : Subring K := (Valued.v).integer

scoped notation:max " 𝒪[" K:max "] " => Valued.integer K

instance (K : Type*) [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [vK : Valued K Γ] : Valued 𝒪[K] Γ := Valued.mk' (vK.v.comap (algebraMap 𝒪[K] K))

-- Is this instance OK? Is it possible for K has many Valued instance for different Γ?
instance integerValuationRing (K : Type*) [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [vK : Valued K Γ] : ValuationRing 𝒪[K] where
  cond' a b := by
    by_cases triv : a = 0 ∨ b = 0
    · use 0
      simp only [mul_zero]
      tauto
    push_neg at triv
    let c := (b : K) / a
    have hc : c ≠ 0 := div_ne_zero ((Subring.coe_eq_zero_iff 𝒪[K]).not.mpr triv.2) ((Subring.coe_eq_zero_iff 𝒪[K]).not.mpr triv.1)
    by_cases h : vK.v c ≤ 1
    · use ⟨c, h⟩
      left
      ext
      field_simp [triv.1]
      ring
    · push_neg at h
      use ⟨c⁻¹, le_of_lt ((Valuation.one_lt_val_iff _ hc).mp h)⟩
      right
      ext
      field_simp [triv.2]
      ring

abbrev maximalIdeal (K : Type*) [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] : Ideal 𝒪[K] := LocalRing.maximalIdeal 𝒪[K]

scoped notation:max " 𝓂[" K:max "] " => maximalIdeal K

theorem maximalIdeal_eq {K : Type*} [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] : 𝓂[K] = (Valued.v).ltIdeal 1 := sorry

abbrev residueField (K : Type*) [Field K] {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] := LocalRing.ResidueField (𝒪[K])

scoped notation:max " 𝓀[" K:max "] " => residueField K

instance {K : Type*} [Field K] [DiscretelyValued K] : Coe 𝒪[K] 𝓀[K] where
  coe := LocalRing.residue 𝒪[K]

end Valued

open Valued

namespace DiscretelyValued

instance {K : Type*} [Field K] [DiscretelyValued K]: DiscretelyValued 𝒪[K] := sorry

instance {K : Type*} [Field K] [DiscretelyValued K]: DiscreteValuationRing 𝒪[K] := sorry



/- `Alternative definition of 𝓂[K]`
abbrev maximalIdeal (K : Type*) [Field K] [DiscretelyValued K] : Ideal 𝒪[K] := LocalRing.maximalIdeal 𝒪[K]

scoped notation:max " 𝓂[" K:max "] " => maximalIdeal K

theorem xxx {K : Type*} [Field K] [DiscretelyValued K] : 𝓂[K] = (Valued.v).ltIdeal 1 := sorry

instance {K : Type*} [Field K] [DiscretelyValued K] : Ideal.IsMaximal ((Valued.v).ltIdeal (1:ℤₘ₀) : Ideal 𝒪[K]) := DiscretelyValued.xxx (K := K) ▸ inferInstance
-/

end DiscretelyValued

-- `theorem: if two discrete valuations are equivalent, then they are equal`

end DVF

/-
1. investigate Maria and Phillip's 今天
2. If exist, copy
  If not, state (今天明天) and proof (mimic 单扩张定理)

  拆分成小定理去证明
-/
