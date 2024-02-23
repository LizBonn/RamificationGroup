import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.WithZero
import Mathlib.Algebra.Order.Group.TypeTags

namespace DiscreteValuation

section examples
-- #synth Coe ℤ (WithTop ℤ)
#synth CoeTC ℤ (WithTop ℤ)

#check ((-1 : ℤ) : WithTop ℤ)

-- #synth Coe ℤ (Multiplicative ℤ)

#check Multiplicative.ofAdd
#check Multiplicative.toAdd


example : ℤₘ₀ := .coe (.ofAdd (2 : ℤ))
-- the order is the same with Z, 0 is bottom element
example : (.coe (.ofAdd (2 : ℤ)) : ℤₘ₀) ≥ .coe (.ofAdd (1 : ℤ))  := by decide

example : (.coe (.ofAdd (3 : ℤ)) : ℤₘ₀) ≥ 0 := by decide

#check (⊥ : ℤₘ₀)
example : 0 = (⊥ : ℤₘ₀) := by rfl

end examples

def ofInt : ℤ →o ℤₘ₀ where
  toFun := .coe
  monotone' _ _ := WithZero.coe_le_coe.mpr

scoped instance : CoeTC ℤ ℤₘ₀ where
  coe := ofInt

-- lots of simp lemmas, related to ofInt, try to copy from `Mathlib.Algebra.Order.Monoid.WithZero.Defs` (WithZero) and `Mathlib.Algebra.Group.TypeTags` (Multiplicative)


end DiscreteValuation
