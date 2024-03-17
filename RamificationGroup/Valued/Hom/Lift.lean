import LocalClassFieldTheory.DiscreteValuationRing.Extensions
import RamificationGroup.Valued.Hom.Defs

open DiscreteValuation Valuation Valued

section check

variable (K : Type*) [Field K] [hv : Valued K ℤₘ₀]
  (L : Type u_1) [Field L] [Algebra K L] [IsDiscrete hv.v] [CompleteSpace K]
  [FiniteDimensional K L]

#check DiscreteValuation.Extension.integralClosure_eq_integer

example : Subalgebra.toSubring (integralClosure (↥(Valuation.valuationSubring hv.v)) L) =
    (valuationSubring (extendedValuation K L)).toSubring := DiscreteValuation.Extension.integralClosure_eq_integer _ _

#synth Algebra 𝒪[K] (integralClosure 𝒪[K] L)

-- #synth Algebra 𝒪[K] ((extendedValuation K L).valuationSubring) -- failed
end check

namespace ValRingHom

variable {R S : Type*} [Ring R] [Ring S] {ΓR ΓS: Type*} [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS] [vR : Valued R ΓR] [vS : Valued S ΓS]

-- `valuation_subring.algebra` instance as algebra Maria and Phillip gives instance on K₀ and L₀ L₀ := valuationSubring of extended valuation
def liftInteger (f : R →+*v S) : vR.v.integer →+*v vS.v.integer where
  toFun x := ⟨f x.val, sorry⟩
  map_one' := by ext; dsimp; exact f.map_one
  map_mul' _ _ := by ext; dsimp; exact f.map_mul _ _
  map_zero' := by ext; dsimp; exact f.map_zero
  map_add' _ _ := by ext; dsimp; exact f.map_add _ _
  monotone' := sorry -- a theorem saying O[K] to K is order preserving
  continuous_toFun := sorry
  val_isEquiv_comap := sorry

variable {K L : Type*} [Field K] [Field L] {ΓK ΓL: Type*} [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL] [vK : Valued K ΓK] [vL : Valued L ΓL] [ValAlgebra K L]

def liftValuationSubring (f : K →+*v L) : 𝒪[K] →+*v 𝒪[L] := ValRingHom.liftInteger f

#synth Semiring K
#synth Semiring L
#synth Semiring 𝒪[K]
#synth Semiring 𝒪[L]
instance liftValuationSubring.IsLocalRingHom (f : K →+*v L) : @IsLocalRingHom 𝒪[K] 𝒪[L] _ _ (liftValuationSubring f) := sorry

end ValRingHom

namespace ValAlgebra

variable {R A : Type*} [CommRing R] [Ring A] {ΓR ΓA: Type*} [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [vR : Valued R ΓR] [vA : Valued A ΓA] [ValAlgebra R A]

-- `valuation_subring.algebra` instance as algebra Maria and Phillip gives instance on K₀ and L₀ L₀ := valuationSubring of extended valuation
instance liftInteger: ValAlgebra vR.v.integer vA.v.integer where
  toFun x := ⟨algebraMap R A x.val, sorry⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  monotone' := sorry
  continuous_toFun := sorry
  val_isEquiv_comap := sorry
  smul := sorry
  commutes' := sorry
  smul_def' := sorry

variable {K L : Type*} [Field K] [Field L] {ΓK ΓL: Type*} [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL] [vK : Valued K ΓK] [vL : Valued L ΓL] [ValAlgebra K L]

instance liftValuationSubring : ValAlgebra 𝒪[K] 𝒪[L] := inferInstanceAs (ValAlgebra vK.v.integer vL.v.integer)

instance liftValuationSubring.IsLocalRingHom : IsLocalRingHom (algebraMap 𝒪[K] 𝒪[L]) := sorry

end ValAlgebra

variable {R A B : Type*} [CommRing R] [Ring A] [Ring B] {ΓR ΓA ΓB : Type*} [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [LinearOrderedCommGroupWithZero ΓB] [vR : Valued R ΓR] [vA : Valued A ΓA] [vB : Valued B ΓB] [ValAlgebra R A] [ValAlgebra R B]

def ValAlgHom.liftInteger  (s : A →ₐv[R] B) : vA.v.integer →ₐv[vR.v.integer] vB.v.integer  where
  toValRingHom := s.toValRingHom.liftInteger
  commutes' := _

def ValAlgEquiv.liftInteger (s : L ≃ₐv[K] L') : 𝒪[L] ≃ₐv[𝒪[K]] 𝒪[L']  := sorry

variable {K L L' : Type*} [Field K] [Field L] [Field L'] {ΓK ΓL ΓL': Type*} [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL] [LinearOrderedCommGroupWithZero ΓL'] [vK : Valued K ΓK] [vL : Valued L ΓL] [vL' : Valued L' ΓL'] [ValAlgebra K L] [ValAlgebra K L'] -- [FiniteDimensional K L]

def ValAlgHom.liftInteger  (s : L →ₐv[K] L') : 𝒪[L] →ₐv[𝒪[K]] 𝒪[L']  := sorry

def ValAlgEquiv.liftInteger (s : L ≃ₐv[K] L') : 𝒪[L] ≃ₐv[𝒪[K]] 𝒪[L']  := sorry

-- instance : Coe (ValAlgHom K L L') (ValAlgHom 𝒪[K] 𝒪[L] 𝒪[L']) := ⟨ValAlgHom.liftInteger⟩

-- instance : Coe (ValAlgEquiv K L L') (ValAlgEquiv 𝒪[K] 𝒪[L] 𝒪[L']) := ⟨ValAlgEquiv.liftInteger⟩

end Valued

/-
def ValAlgHom.liftValuationIntegerQuotientleIdeal (s : L →ₐv[K] L) (γ : ΓL') : 𝒪[L]⧸(vL'.v.leIdeal γ) →ₐ[𝒪[K]] 𝒪[L']⧸(vL.leIdeal γ) := sorry

def ValAlgIso.liftValuationIntegerQuotientleIdeal (s : L ≃ₐ[K] L) (γ : ΓL) : (𝒪[vL]⧸(vL.leIdeal γ)) ≃ₐ[𝒪[vK]] (𝒪[vL]⧸(vL.leIdeal γ)) := sorry

-- `LT version`

def AlgHom.liftResidueField (s : L →ₐ[K] L) : 𝓀[vL] →ₐ[𝓀[vK]] 𝓀[vL] := sorry

def AlgEquiv.liftResidueField (s : L ≃ₐ[K] L) : 𝓀[vL] ≃ₐ[𝓀[vK]] 𝓀[vL] := sorry

-/
