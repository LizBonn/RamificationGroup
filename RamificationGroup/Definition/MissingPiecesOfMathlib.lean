import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.Algebra.Ring.Basic
/-!
# Missing Pieces of Mathlib

In this file, we collect missing theorems, instances as prequisite of this project. Theorems in this file should be added to mathlib file scatterly into each file.
-/

variable {R: Type*} [Ring R]
-- variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]

namespace ValuationTopology
variable [CommRing R] [IsDomain R] [ValuationRing R]

scoped instance: TopologicalSpace R := sorry

scoped instance: TopologicalRing R := sorry

end ValuationTopology


-- open ValuationTopology
-- variable [CommRing R] [IsDomain R] [ValuationRing R]
-- #synth TopologicalRing R
