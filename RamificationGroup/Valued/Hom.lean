import Mathlib.Topology.Algebra.Valuation

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


-- `Hom should be a folder, the following section should be in a separate file`
section

/- `Update this!`

-- `key theorem: If L/K is a finite field extension + more conditions, then any 2 extension of valuations from K on L are equivalent`
theorem Valuation.isEquiv_of_finiteDimensional_of_valuationExtension {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {Γ Γ₁ Γ₂ : Type*} [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Γ₁]
[LinearOrderedCommGroupWithZero Γ₂]
(v : Valuation K Γ) (v₁ : Valuation L Γ₁) (v₂ : Valuation L Γ₂) [ValuationExtension v v₁] [ValuationExtension v v₂] : v₁.IsEquiv v₂ := sorry

-- need more conditions
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {ΓK ΓL: Type*} [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL] (vK : Valuation K ΓK) (vL : Valuation L ΓL) [ValuationExtension vK vL]

theorem Valuation.preserveValuation_of_finiteDimensional_algebra_hom  (s : L →ₐ[K] L) : PreserveValuation vL vL s := sorry
-- vL.IsEquiv (vL.comap s) := sorry
-- (s : L ≃ₐ[K] L)

def AlgHom.liftValuationInteger (s : L →ₐ[K] L) : 𝒪[vL] →ₐ[𝒪[vK]] 𝒪[vL] := sorry

def AlgEquiv.liftValuationInteger (s : L ≃ₐ[K] L) : 𝒪[vL] ≃ₐ[𝒪[vK]] 𝒪[vL] := sorry

-- `If preserve valuation is a class, this AlgHom.liftValuationInteger should be make into a Coe instance`

def AlgHom.liftValuationIntegerQuotientLEIdeal (s : L →ₐ[K] L) (γ : ΓL) : 𝒪[vL]⧸(vL.LEIdeal γ) →ₐ[𝒪[vK]] 𝒪[vL]⧸(vL.LEIdeal γ) := sorry

def AlgEquiv.liftValuationIntegerQuotientLEIdeal (s : L ≃ₐ[K] L) (γ : ΓL) : (𝒪[vL]⧸(vL.LEIdeal γ)) ≃ₐ[𝒪[vK]] (𝒪[vL]⧸(vL.LEIdeal γ)) := sorry

-- `LT version`

def AlgHom.liftResidueField (s : L →ₐ[K] L) : 𝓀[vL] →ₐ[𝓀[vK]] 𝓀[vL] := sorry

def AlgEquiv.liftResidueField (s : L ≃ₐ[K] L) : 𝓀[vL] ≃ₐ[𝓀[vK]] 𝓀[vL] := sorry
-/

-- Unique instance in the case of Local Fields, which comes from uniqueness of extension of valuation.

end
