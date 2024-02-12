import Mathlib.RingTheory.Valuation.Integers
import RamificationGroup.Preliminary.DiscreteValuation


#check Valuation.integer

-- Mathlib.RingTheory.Valuation.Integers
def Valuation.LEIdeal {R : Type*}  {Γ₀ : outParam Type*}  [Ring R] [LinearOrderedCommGroupWithZero Γ₀]  (v : Valuation R Γ₀) (γ : Γ₀) : Ideal (Valuation.integer v) := sorry
-- when gamma < 1, the ideal is whole ring

def Valuation.LTIdeal {R : Type*}  {Γ₀ : outParam Type*}  [Ring R] [LinearOrderedCommGroupWithZero Γ₀]  (v : Valuation R Γ₀) (γ : Γ₀) : Ideal (Valuation.integer v) := sorry
-- when gamma < 1, the ideal is whole ring

-- inclusion relation,...

namespace DiscreteValuation
-- `In Discrete Valuation Ring, relation between LT LE Ideal`

theorem LEIdeal_eq_LTIdeal_add_one {R : Type*}  [Ring R] (v : Valuation R ℤₘ₀) (n : ℤ) : v.LEIdeal (ofZ n) = v.LTIdeal (ofZ $ n + 1) := sorry

end DiscreteValuation
