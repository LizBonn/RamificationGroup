import Mathlib.Topology.Algebra.Valuation
import RamificationGroup.Valued.Definitions
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Algebra.Order.Hom.Ring

open DiscreteValuation

structure ValRingHom (R S : Type*) {ΓR ΓS : outParam Type*} [Ring R] [Ring S]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS]
  [vR : Valued R ΓR] [vS : Valued S ΓS] extends OrderRingHom R S, ContinuousMap R S where
  val_isEquiv_comap : vR.v.IsEquiv (vS.v.comap toOrderRingHom.toRingHom)

infixr:25 " →+*v " => ValRingHom -- 25 = Binding power of `→+*`

structure ValRingEquiv (R S : Type*) {ΓR ΓS : outParam Type*} [Ring R] [Ring S]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS]
  [vR : Valued R ΓR] [vS : Valued S ΓS] extends OrderRingIso R S, Homeomorph R S where
  val_isEquiv_comap : vR.v.IsEquiv (vS.v.comap toOrderRingIso.toOrderRingHom.toRingHom)

infixr:25 " ≃+*v " => ValRingEquiv

variable (R S : Type*) {ΓR ΓS : outParam Type*} [Ring R] [Ring S]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS]
  [vR : Valued R ΓR] [vS : Valued S ΓS]

def ValRingHom.mk' (f : R →+* S) (hf : vR.v.IsEquiv (vS.v.comap f)) : R →+*v S := sorry

def ValRingEquiv.mk' (f : R ≃+* S) (hf : vR.v.IsEquiv (vS.v.comap f)) : R ≃+*v S := sorry

-- ValRingHomClass
-- ValRingIsoClass

-- `copy lemmas in OrderRingHom`



class ValAlgebra (R A : Type*) {ΓR ΓA : outParam Type*} [CommRing R] [Ring A] [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [vR : Valued R ΓR] [vA : Valued A ΓA] extends ValRingHom R A, Algebra R A

def ValRingHom.toValAlgebra {R A : Type*} {ΓR ΓA : outParam Type*} [CommRing R] [CommRing A] [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [Valued R ΓR] [Valued A ΓA] (f : R →+*v A) : ValAlgebra R A where
  toValRingHom := f
  smul := f.toRingHom.toAlgebra.smul
  smul_def' := f.toRingHom.toAlgebra.smul_def'
  commutes' := f.toRingHom.toAlgebra.commutes'
-- `copy more lemmas in Algebra`


structure ValAlgHom (R A B : Type*) [CommRing R] [Ring A] [Ring B] {ΓR ΓA ΓB : outParam Type*} [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [LinearOrderedCommGroupWithZero ΓB] [Valued R ΓR] [Valued A ΓA] [Valued B ΓB] [ValAlgebra R A] [ValAlgebra R B] extends ValRingHom A B, AlgHom R A B

structure ValAlgEquiv (R A B : Type*) [CommRing R] [Ring A] [Ring B] {ΓR ΓA ΓB : outParam Type*} [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [LinearOrderedCommGroupWithZero ΓB] [Valued R ΓR] [Valued A ΓA] [Valued B ΓB] [ValAlgebra R A] [ValAlgebra R B] extends ValRingEquiv A B, AlgEquiv R A B

notation:25 A " →ₐv[" R "] " B => ValAlgHom R A B

notation:25 A " ≃ₐv[" R "] " B => ValAlgEquiv R A B

-- ValAlgHomClass
-- ValAlgIsoClass

-- `copy lemmas in MonoidWithZeroHom` or `OrderRingHom`
-- -- coercions

variable (R A B : Type*) [CommRing R] [Ring A] [Ring B] {ΓR ΓA ΓB : outParam Type*} [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [LinearOrderedCommGroupWithZero ΓB] [Valued R ΓR] [Valued A ΓA] [Valued B ΓB] [ValAlgebra R A] [ValAlgebra R B]
#synth CoeFun (AlgEquiv R A B) (fun _ => (A → B))
instance : FunLike (ValAlgEquiv R A B) A B where
  coe f := f.toFun
  coe_injective' := sorry

-- -- structures on ValRingHom/Iso
instance {R A B : Type*} [CommRing R] [Ring A] [Ring B] {ΓR ΓA ΓB : outParam Type*} [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [LinearOrderedCommGroupWithZero ΓB] [Valued R ΓR] [Valued A ΓA] [Valued B ΓB] [ValAlgebra R A] [ValAlgebra R B] : Group (ValAlgEquiv R A B) := sorry
