import LocalClassFieldTheory.DiscreteValuationRing.Extensions
import RamificationGroup.Valued.Defs

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
  map_one' := by ext; exact f.map_one
  map_mul' _ _ := by ext; exact f.map_mul _ _
  map_zero' := by ext; exact f.map_zero
  map_add' _ _ := by ext; exact f.map_add _ _
  monotone' := sorry -- a theorem saying O[K] to K is order preserving
  continuous_toFun := sorry
  val_isEquiv_comap' := sorry

variable {K L : Type*} [Field K] [Field L] {ΓK ΓL: outParam Type*} [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL] [vK : Valued K ΓK] [vL : Valued L ΓL] [ValAlgebra K L]

def liftValuationSubring (f : K →+*v L) : 𝒪[K] →+*v 𝒪[L] := f.liftInteger

#synth LocalRing 𝒪[K]
#synth LocalRing 𝒪[L]

instance liftValuationSubring.IsLocalRingHom {f : K →+*v L} : IsLocalRingHom (f.liftValuationSubring : 𝒪[K] →+* 𝒪[L]) := sorry

def liftResidueField (f : K →+*v L) : 𝓀[K] →+* 𝓀[L] := LocalRing.ResidueField.map (f.liftValuationSubring) -- TODO? : Should residue field be equipped with trivial valuation and enhance this to a ValRingHom?

variable (f : K →+*v L)(s : 𝒪[K] →+*v 𝒪[L])
#check (s : 𝒪[K] →+* 𝒪[L])
#check f.liftValuationSubring
-- #synth IsLocalRingHom (liftValuationSubring f)
-- #synth IsLocalRingHom (f.liftValuationSubring.toRingHom) -- coe is not def eq to .toRingHom
#check liftValuationSubring.IsLocalRingHom

end ValRingHom

namespace ValRingEquiv

variable {R S : Type*} [Ring R] [Ring S] {ΓR ΓS: Type*} [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS] [vR : Valued R ΓR] [vS : Valued S ΓS]

-- `valuation_subring.algebra` instance as algebra Maria and Phillip gives instance on K₀ and L₀ L₀ := valuationSubring of extended valuation
def liftInteger (f : R ≃+*v S) : vR.v.integer ≃+*v vS.v.integer where
  toFun x := ⟨f x.val, sorry⟩
  invFun y := ⟨f.invFun y.val, sorry⟩
  left_inv _ := by ext; exact f.left_inv _
  right_inv _ := by ext; exact f.right_inv _
  map_mul' _ _ := by ext; exact f.map_mul' _ _
  map_add' _ _ := by ext; exact f.map_add' _ _
  map_le_map_iff' := sorry
  continuous_toFun := sorry
  continuous_invFun := sorry
  val_isEquiv_comap' := sorry


variable {K L : Type*} [Field K] [Field L] {ΓK ΓL: outParam Type*} [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL] [vK : Valued K ΓK] [vL : Valued L ΓL] [ValAlgebra K L]

def liftValuationSubring (f : K ≃+*v L) : 𝒪[K] ≃+*v 𝒪[L] := f.liftInteger

instance liftValuationSubring.IsLocalRingHom {f : K ≃+*v L} : IsLocalRingHom (f.liftValuationSubring : 𝒪[K] →+* 𝒪[L]) := inferInstanceAs (_root_.IsLocalRingHom (ValRingHom.liftValuationSubring (f : K →+*v L)))

def liftResidueField (f : K ≃+*v L) : 𝓀[K] ≃+* 𝓀[L] := LocalRing.ResidueField.mapEquiv (f.liftValuationSubring) -- TODO? : Should residue field be equipped with trivial valuation and enhance this to a ValRingHom?

end ValRingEquiv

namespace ValAlgebra

variable {R A : Type*} [CommRing R] [Ring A] {ΓR ΓA: Type*} [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [vR : Valued R ΓR] [vA : Valued A ΓA] [ValAlgebra R A]

-- `valuation_subring.algebra` instance as algebra Maria and Phillip gives instance on K₀ and L₀ L₀ := valuationSubring of extended valuation
instance liftInteger: ValAlgebra vR.v.integer vA.v.integer where
  toValRingHom := ValAlgebra.toValRingHom.liftInteger
  smul := fun ⟨r, _⟩ ⟨a, _⟩ => ⟨r • a, sorry⟩
  commutes' := fun ⟨r, _⟩ ⟨a, _⟩ => by ext; exact ValAlgebra.commutes' r a
  smul_def' := fun ⟨r, _⟩ ⟨a, _⟩ => by ext; exact ValAlgebra.smul_def' r a

variable {K L : Type*} [Field K] [Field L] {ΓK ΓL: Type*} [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL] [vK : Valued K ΓK] [vL : Valued L ΓL] [i : ValAlgebra K L]

instance liftValuationSubring : ValAlgebra 𝒪[K] 𝒪[L] := inferInstanceAs (ValAlgebra vK.v.integer vL.v.integer)

instance liftValuationSubring.IsLocalRingHom : IsLocalRingHom (algebraMap 𝒪[K] 𝒪[L]) := inferInstanceAs (_root_.IsLocalRingHom (i.toValRingHom).liftValuationSubring)

--TODO : `Should add IsLocalAlgebra or LocalAlgebra to Mathlib`
instance liftResidueField : Algebra 𝓀[K] 𝓀[L] where
  smul := sorry -- define this carefully, quotient from original action on 𝒪!!
  toRingHom := LocalRing.ResidueField.map ((valAlgebraMap K L).liftValuationSubring)
  commutes' := sorry
  smul_def' := sorry -- TODO? : Should residue field be equipped with trivial valuation and enhance this to a ValRingHom?

end ValAlgebra

namespace ValAlgHom

variable {R A B : Type*} [CommRing R] [Ring A] [Ring B] {ΓR ΓA ΓB : Type*} [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [LinearOrderedCommGroupWithZero ΓB] [vR : Valued R ΓR] [vA : Valued A ΓA] [vB : Valued B ΓB] [ValAlgebra R A] [ValAlgebra R B]

def liftInteger (s : A →ₐv[R] B) : vA.v.integer →ₐv[vR.v.integer] vB.v.integer where
  toValRingHom := s.toValRingHom.liftInteger
  commutes' _ := by ext; exact s.commutes' _

variable {K L L' : Type*} [Field K] [Field L] [Field L'] {ΓK ΓL ΓL': Type*} [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL] [LinearOrderedCommGroupWithZero ΓL'] [vK : Valued K ΓK] [vL : Valued L ΓL] [vL' : Valued L' ΓL'] [ValAlgebra K L] [ValAlgebra K L'] -- [FiniteDimensional K L]

def liftValuationSubring (f : L →ₐv[K] L') : 𝒪[L] →ₐv[𝒪[K]] 𝒪[L'] := f.liftInteger

instance liftValuationSubring.IsLocalRingHom {s : L →ₐv[K] L'}: IsLocalRingHom ((s.liftValuationSubring : 𝒪[L] →+*v 𝒪[L']) : 𝒪[L] →+* 𝒪[L']) := inferInstanceAs (_root_.IsLocalRingHom (s : L →+*v L').liftValuationSubring)

def liftResidueField (f : L →ₐv[K] L') : 𝓀[L] →ₐ[𝓀[K]] 𝓀[L'] where
  toRingHom := ValRingHom.liftResidueField f
  commutes' := sorry -- by apply Quotient.ind

end ValAlgHom

namespace ValAlgEquiv

variable {R A B : Type*} [CommRing R] [Ring A] [Ring B] {ΓR ΓA ΓB : Type*} [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [LinearOrderedCommGroupWithZero ΓB] [vR : Valued R ΓR] [vA : Valued A ΓA] [vB : Valued B ΓB] [ValAlgebra R A] [ValAlgebra R B]

def liftInteger (s : A ≃ₐv[R] B) : vA.v.integer ≃ₐv[vR.v.integer] vB.v.integer where
  toValRingEquiv := s.toValRingEquiv.liftInteger
  commutes' _ := by ext; exact s.commutes' _

variable {K L L' : Type*} [Field K] [Field L] [Field L'] {ΓK ΓL ΓL': Type*} [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL] [LinearOrderedCommGroupWithZero ΓL'] [vK : Valued K ΓK] [vL : Valued L ΓL] [vL' : Valued L' ΓL'] [ValAlgebra K L] [ValAlgebra K L'] -- [FiniteDimensional K L]

def liftValuationSubring (f : L ≃ₐv[K] L') : 𝒪[L] ≃ₐv[𝒪[K]] 𝒪[L'] := f.liftInteger

variable (s : L ≃ₐv[K] L')
#synth IsLocalRingHom (((s : L →ₐv[K] L') : L →+*v L').liftValuationSubring : 𝒪[L] →+* 𝒪[L'])
-- #synth IsLocalRingHom (s.liftValuationSubring : 𝒪[L] →+* 𝒪[L']) -- this fails, this is the other way of a diamond, rfl to above but lean does not infer instances across rfl.
instance liftValuationSubring.IsLocalRingHom {s : L ≃ₐv[K] L'}: IsLocalRingHom ((s.liftValuationSubring : 𝒪[L] ≃+*v 𝒪[L']) : 𝒪[L] →+* 𝒪[L']) := inferInstanceAs (_root_.IsLocalRingHom ((s : L ≃+*v L') : L →+*v L').liftValuationSubring)

def liftResidueField (f : L ≃ₐv[K] L') : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L'] where
  toEquiv := f.toValRingEquiv.liftResidueField
  map_mul' := f.toValRingEquiv.liftResidueField.map_mul
  map_add' := f.toValRingEquiv.liftResidueField.map_add
  commutes' := sorry

-- should these be made into instances? `𝒪` and `𝓀`
-- instance : Coe (ValAlgHom K L L') (ValAlgHom 𝒪[K] 𝒪[L] 𝒪[L']) := ⟨ValAlgHom.liftInteger⟩

-- instance : Coe (ValAlgEquiv K L L') (ValAlgEquiv 𝒪[K] 𝒪[L] 𝒪[L']) := ⟨ValAlgEquiv.liftInteger⟩

-- instance ...

end ValAlgEquiv

/-
def ValAlgHom.liftValuationIntegerQuotientleIdeal (s : L →ₐv[K] L) (γ : ΓL') : 𝒪[L]⧸(vL'.v.leIdeal γ) →ₐ[𝒪[K]] 𝒪[L']⧸(vL.leIdeal γ) := sorry

def ValAlgIso.liftValuationIntegerQuotientleIdeal (s : L ≃ₐ[K] L) (γ : ΓL) : (𝒪[vL]⧸(vL.leIdeal γ)) ≃ₐ[𝒪[vK]] (𝒪[vL]⧸(vL.leIdeal γ)) := sorry

-- `LT version`

def AlgHom.liftResidueField (s : L →ₐ[K] L) : 𝓀[vL] →ₐ[𝓀[vK]] 𝓀[vL] := sorry

def AlgEquiv.liftResidueField (s : L ≃ₐ[K] L) : 𝓀[vL] ≃ₐ[𝓀[vK]] 𝓀[vL] := sorry

-/

namespace ValAlgEquiv

section

variable {K L L' : Type*} [CommRing K] [Ring L] [Ring L'] {ΓK ΓL ΓL': Type*} [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL] [LinearOrderedCommGroupWithZero ΓL'] [vK : Valued K ΓK] [vL : Valued L ΓL] [vL' : Valued L' ΓL'] [ValAlgebra K L] [ValAlgebra K L']

@[simp]
theorem coe_liftInteger {s : L ≃ₐv[K] L} {x : vL.v.integer} : ((s.liftInteger x) : L) = s x := rfl

@[simp]
theorem liftInteger_refl : (.refl : L ≃ₐv[K] L).liftInteger = .refl := by
  ext
  rfl

end

section

variable {K L L' : Type*} [CommRing K] [Field L] [Ring L'] {ΓK ΓL ΓL': Type*} [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL] [LinearOrderedCommGroupWithZero ΓL'] [vK : Valued K ΓK] [vL : Valued L ΓL] [vL' : Valued L' ΓL'] [ValAlgebra K L] [ValAlgebra K L']

@[simp]
theorem eq_refl_of_liftInteger_eq_refl {s : L ≃ₐv[K] L} : s.liftInteger = .refl ↔ s = .refl := by
  constructor <;>
  intro h
  · ext l
    obtain ⟨x, ⟨y, ⟨_, rfl⟩⟩⟩ := IsFractionRing.div_surjective l (A := 𝒪[L])
    calc
    _ = ((s.liftInteger x) : L) / s.liftInteger y := by simp
    _ = _ := by simp [h]
  · simp [h]

end

end ValAlgEquiv
