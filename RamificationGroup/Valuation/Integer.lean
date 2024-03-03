import Mathlib.RingTheory.Valuation.Integers
import RamificationGroup.Preliminary.DiscreteValuation


#check Valuation.integer

#check Valuation.ltAddSubgroup -- `Make use of this!!`

-- Mathlib.RingTheory.Valuation.Integers
def Valuation.leIdeal {R : Type*} {Γ₀ : outParam Type*}  [Ring R] 
  [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) (γ : Γ₀) : Ideal (v.integer) where
  carrier := {x : v.integer | v x ≤ γ}
  add_mem' ha hb := .trans (v.map_add_le_max' _ _) (max_le ha hb)
  zero_mem' := by
    show v 0 ≤ γ
    simp only [map_zero, zero_le']
  smul_mem' c a ha := by
    show v (c * a) ≤ γ
    calc
      _ = v c * v a := v.map_mul' _ _
      _ ≤ 1 * γ := mul_le_mul' c.2 ha
      _ = γ := one_mul _

theorem Valuation.leIdeal_eq_top {R : Type*} {Γ₀ : outParam Type*}  [Ring R] 
  [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) {γ : Γ₀} (h : 1 ≤ γ) : v.leIdeal γ = ⊤ := sorry
-- when gamma ≥ 1, the ideal is whole ring

-- special value when γ = 0
def Valuation.ltIdeal {R : Type*}  {Γ₀ : outParam Type*}  [Ring R] [LinearOrderedCommGroupWithZero Γ₀]  (v : Valuation R Γ₀) (γ : Γ₀) : Ideal (Valuation.integer v) := if h : γ = 0 then ⊥ else {  
  carrier := {x : v.integer | v x < γ},
  add_mem' := fun ha hb ↦ lt_of_le_of_lt (v.map_add_le_max' _ _) (max_lt ha hb),
  zero_mem' := by
    show v 0 < γ
    simpa only [map_zero, zero_lt_iff],
  smul_mem' := fun c a ha ↦ by
    show v (c * a) < γ
    calc
      _ = v c * v a := v.map_mul' _ _
      _ ≤ 1 * v a := mul_le_mul' c.2 (le_refl _)
      _ = v a := one_mul _
      _ < γ := ha
  }

theorem Valuation.ltIdeal_eq_top {R : Type*} {Γ₀ : outParam Type*}  [Ring R] 
  [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) {γ : Γ₀} (h : 1 < γ) : v.ltIdeal γ = ⊤ := sorry
-- when gamma < 1, the ideal is whole ring

-- inclusion relation,...

namespace DiscreteValuation
-- `In Discrete Valuation Ring, relation between LT LE Ideal`

theorem leIdeal_eq_ltIdeal_add_one {R : Type*}  [Ring R] (v : Valuation R ℤₘ₀) (n : ℤ) : v.leIdeal (ofInt n) = v.ltIdeal (ofInt (n + 1)) := sorry

end DiscreteValuation
