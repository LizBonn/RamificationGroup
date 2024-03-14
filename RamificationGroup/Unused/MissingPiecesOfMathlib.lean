import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Valuation
import Mathlib.Data.Real.Basic
/-!
# Missing Pieces of Mathlib

In this file, we collect missing theorems, instances as prequisite of this project. Theorems in this file should be added to mathlib file scatterly into each file.
-/

variable (R: Type*)
-- variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]

namespace ValuationTopology
variable [CommRing R] [IsDomain R] [ValuationRing R]

/-- The preorder of divisibility associated to a valuation ring, i.e. `a ≤ b` if there exist `c`, such that `a * c = b`. -/
scoped instance : Preorder R where
 le a b := ∃ c, a * c = b
 le_refl _ := ⟨1, mul_one _⟩
 le_trans _ _ _ := fun ⟨u, h⟩ ⟨v, g⟩ => ⟨u * v, by rw [← g, ← h]; ring⟩

/-- The topology on a valuation ring `R` is defined to be the topology associated to the preorder of divisibility.-/
scoped instance : TopologicalSpace R := Preorder.topology R

scoped instance : OrderTopology R := ⟨rfl⟩

scoped instance : UniformSpace R where
  uniformity := sorry
  refl := sorry
  symm := sorry
  comp := sorry
  isOpen_uniformity := sorry


/-!
-- the following is missed in `Mathlib.RingTheory.Valuation.ValuationRing`

def ValuationRing.setoid : Setoid R where
  r a b := a ≤ b ∧ b ≤ a
  -- 2 elements is equiv if both a ≤ b and b ≤ a
  iseqv := sorry


def ValuationRing.ValueMonoid := Quotient (ValuationRing.setoid R) -- this is really a monoid with zero

instance : LinearOrderedCommMonoidWithZero (ValuationRing.ValueMonoid R) := sorry

scoped instance : Valued R (ValuationRing.ValueMonoid R) := _

-- `Valued` uses Group instead of Monoid... `Maybe the correct way is to generalize mathlib's valued to monoid instead of group???`
-/


end ValuationTopology



section OrderHom

--class OrderMonoidHom (A B : Type*) [Preorder A] [Preorder B] [MulOneClass A] [MulOneClass B] extends OrderHom A B, MonoidHom A B

infix : 50 " →*o " => OrderMonoidHom

#check MonoidWithZeroHom

--class OrderMonoidWithZeroHom (A B : Type*) [Preorder A] [Preorder B] [MulZeroOneClass A] [MulZeroOneClass B] extends OrderHom A B, MonoidWithZeroHom A B

variable {A B : Type*} [LinearOrderedCommMonoidWithZero A] [LinearOrderedCommMonoidWithZero B]
#check OrderMonoidWithZeroHom A B

end OrderHom


/-
class CompleteDiscreteValuationRing (R : Type*) [CommRing R] [IsDomain R] extends CompleteValuationRing R where
  is_discrete : sorry

-- Maybe these two definition is not so necessary
class CompleteValuationField (R : Type*) [Field R] extends CompleteValuationRing R

class CompleteDiscreteValuationField (R : Type*) [Field R] extends CompleteValuationRing R
-/




open Subgroup
section

variable {G : Type*} [Group G] (H L K : Subgroup G)

noncomputable def relindex' : ℚ :=
  (K.index : ℚ) / (H.index: ℚ)

end
