import Mathlib.Topology.Algebra.Valuation
import RamificationGroup.Valued.Definitions
import Mathlib.LinearAlgebra.FiniteDimensional

open DiscreteValuation

@[ext]
structure ValRingHom (R S : Type*) {ΓR ΓS : outParam Type*} [Ring R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS] [vR : Valued R ΓR] [vS : Valued S ΓS] extends RingHom R S where
  val_isEquiv : vR.v.IsEquiv (vS.v.comap toRingHom)

-- ValRingIso

infixr:25 " →+*v " => ValRingHom -- 25 = Binding power of `→+*`

-- infixr:25 " ≃+*v " => ValRingHom

-- ValRingHomClass
-- ValRingIsoClass

-- `copy lemmas in OrderRingHom`

class ValAlgebra (R A : Type*) {ΓR ΓA : outParam Type*} [CommRing R] [Ring A] [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [vR : Valued R ΓR] [vA : Valued A ΓA] extends Algebra R A, ValRingHom R A

-- `copy lemmas in Algebra`

@[ext]
structure ValAlgHom (R A B : Type*) [CommRing R] [Ring A] [Ring B] {ΓR ΓA ΓB : outParam Type*} [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [LinearOrderedCommGroupWithZero ΓB] [Valued R ΓR] [Valued A ΓA] [Valued B ΓB] [ValAlgebra R A] [ValAlgebra R B] extends AlgHom R A B, ValRingHom A B

-- ValAlgIso

notation:25 A " →ₐv[" R "] " B => ValAlgHom R A B

-- notation:25 A " ≃ₐv[" R "] " B => ValAlgIso R A B

-- ValAlgHomClass
-- ValAlgIsoClass

-- `copy lemmas in MonoidWithZeroHom`
