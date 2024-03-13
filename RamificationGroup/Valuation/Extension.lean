/-
TODO: put the two cases of together to give PowerBasis in general.

# of WARNINGs : 3

does `Module.finite` implies `FiniteDimensional`?

elim of `∨` ?

-/
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.NumberTheory.RamificationInertia
import RamificationGroup.Valuation.SubAlgEquiv

variable (A : Type*) [CommRing A] [LocalRing A]
variable (B : Type*) [CommRing B] [LocalRing B]
variable [Algebra A B] [IsLocalRingHom (algebraMap A B)]

open LocalRing Classical

noncomputable section

def LocalRing.ramificationIdx : ℕ := Ideal.ramificationIdx (algebraMap A B) (maximalIdeal A) (maximalIdeal B)

def LocalRing.inertiaDeg : ℕ := Ideal.inertiaDeg (algebraMap A B) (maximalIdeal A) (maximalIdeal B)

/- WARNING : `Smul` of this `Algebra` might be incompatible -/
instance LocalRing.instAlgebraResidue: Algebra (ResidueField A) (ResidueField B) := (ResidueField.map (algebraMap A B)).toAlgebra

variable [IsDomain A] [DiscreteValuationRing A] [IsDomain B] [DiscreteValuationRing B]

namespace ExtDVR

def rankExtDVR : ℕ := (ramificationIdx A B) * (inertiaDeg A B)

variable [Module.Finite A B] [IsSeparable (ResidueField A) (ResidueField B)]

instance instFiniteExtResidue : FiniteDimensional (ResidueField A) (ResidueField B) := sorry

open IntermediateField Polynomial Classical

variable {A} {B}
-- `x` : a lift of a primitive element of `k_B/k_A`
-- WARNING: `hx` might not be a good statement
variable {x : B} (hx : (ResidueField A)⟮residue B x⟯ = ⊤)
-- `f` : a monic polynomial with `A`-coeff that reduce to the minpoly of `x : k_B` over `k_A`
variable {f : A[X]} (h_monic : Monic f) (h_red : f.map (residue A) = minpoly (ResidueField A) (residue B x))
-- `ϖ` : a uniformizer `ϖ` of `B`
variable {ϖ : B} (hϖ : Irreducible ϖ)

theorem fx_ne_0 : f.eval₂ (algebraMap A B) x ≠ 0 := sorry

/-some possibly useful thms are listed below-/
#check Field.powerBasisOfFiniteOfSeparable (ResidueField A) (ResidueField B)
#check Algebra.adjoin.powerBasis'
#check IsIntegral.of_finite
#check Algebra.adjoin
-- #check IsPrimitiveRoot.adjoinEquivRingOfIntegers
-- #check IsPrimitiveRoot.integralPowerBasis
/-
lemma 4 states that the lifting `x` could be choose so that `f x` is a uniformizer of `B`.
Proof:
  choose an arbitary lifting `x`.
  If `f x` is a uniformizer, it is done.
  otherwise, `f x` lies have valuation ≥ 2, and `f (x + ϖ)` satisfy the condition.
The following thm is the `otherwise` case.
-/

theorem lemma4_val_ge_2 (h_fx : ¬Irreducible (f.eval₂ (algebraMap A B) x)) : Irreducible (f.eval₂ (algebraMap A B) (x + ϖ)) := sorry

/-
The following two theorem states that `B = A[x]` if `f x` is a uniformizer;
otherwise `B = A[x + ϖ]`.
However, this does not imply that `B` has a finite `A`-basis.
-/
theorem thm_val_1 (h_fx : Irreducible (f.eval₂ (algebraMap A B) x)) : Algebra.adjoin A {x} = ⊤ := sorry

theorem thm_val_ge_2 (h_fx : ¬Irreducible (f.eval₂ (algebraMap A B) x)) : Algebra.adjoin A {x + ϖ} = ⊤ := sorry

variable (A) (B)

theorem exists_primitive : ∃x : B, Algebra.adjoin A {x} = ⊤ := sorry

-- WARNING: inst conflict
variable [NoZeroSMulDivisors A B]

-- #check choose_spec
-- def PowerBasisExtDVR_val_1 (h_fx : Irreducible (f.eval₂ (algebraMap A B) x)) : PowerBasis A B :=
--   (Algebra.adjoin.powerBasis' (IsIntegral.of_finite A x) ).map (equiv_val_1' h_fx)

def PowerBasisExtDVR : PowerBasis A B :=
  (Algebra.adjoin.powerBasis' (IsIntegral.of_finite _ _)).map
    (AlgEquiv.ofTop (choose_spec (exists_primitive _ _)))

end ExtDVR
