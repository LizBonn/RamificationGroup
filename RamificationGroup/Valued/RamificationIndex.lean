import RamificationGroup.Valued.Definitions
import RamificationGroup.Valued.Hom.Basic
import RamificationGroup.Valued.Hom.Discrete

open DiscreteValuation

namespace ValRingHom

variable {R S : Type*} {ΓR ΓS : outParam Type*} [Ring R] [Ring S] [DiscretelyValued R] [DiscretelyValued S]

def ramificationIndex {R S : Type*} {ΓR ΓS : outParam Type*} [Ring R] [Ring S] [DiscretelyValued R] [DiscretelyValued S] (f : ValRingHom R S) : ℕ := sorry -- min of .v (image of elements of R that has val > 1 in S)
-- ℕ, not WithTop ℕ
