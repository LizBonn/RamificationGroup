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

section local_ring
def LocalRing.ramificationIdx : ℕ := Ideal.ramificationIdx (algebraMap A B) (maximalIdeal A) (maximalIdeal B)

def LocalRing.inertiaDeg : ℕ := Ideal.inertiaDeg (algebraMap A B) (maximalIdeal A) (maximalIdeal B)

/- WARNING : `Smul` of this `Algebra` might be incompatible -/
instance LocalRing.instAlgebraResidue: Algebra (ResidueField A) (ResidueField B) := (ResidueField.map (algebraMap A B)).toAlgebra

end local_ring


namespace ExtDVR

variable [IsDomain A] [DiscreteValuationRing A] [IsDomain B] [DiscreteValuationRing B]

variable [Module.Finite A B] [IsSeparable (ResidueField A) (ResidueField B)]

instance instFiniteExtResidue : FiniteDimensional (ResidueField A) (ResidueField B) := sorry

open IntermediateField Polynomial Classical

#check Field.exists_primitive_element
theorem exists_x : ∃x : B, (ResidueField A)⟮residue B x⟯ = ⊤ := sorry

#check IsIntegral.of_finite
#check RingHom.IsIntegralElem (algebraMap A B)
theorem exists_f_of_x (x : B) : ∃f : A[X], Monic f ∧ f.map (residue A) = minpoly (ResidueField A) (residue B x) := sorry


variable {A} {B}

section x_and_f
-- `x` : a lift of a primitive element of `k_B/k_A`
-- WARNING: `hx` might not be a good statement
variable {x : B} (hx : (ResidueField A)⟮residue B x⟯ = ⊤)
-- `f` : a monic polynomial with `A`-coeff that reduces to the minpoly of `x : k_B` over `k_A`
variable {f : A[X]} (h_monic : Monic f) (h_red : f.map (residue A) = minpoly (ResidueField A) (residue B x))
-- `ϖ` : a uniformizer `ϖ` of `B`
variable {ϖ : B} (hϖ : Irreducible ϖ)


/-some possibly useful thms are listed below-/
#check Algebra.adjoin.powerBasis'
#check IsIntegral.of_finite
#check Algebra.adjoin
-- #check IsPrimitiveRoot.adjoinEquivRingOfIntegers
-- #check IsPrimitiveRoot.integralPowerBasis

/-
lemma 3 states that `xⁱϖʲ` with finite `i j`'s form a `A`-basis of `B`.
The next theorem is alternate and weaker version of lemma 3,
stating that `A[x, ϖ] = B`.
-/
theorem lemma3_weak' : Algebra.adjoin A {x, ϖ} = ⊤ := sorry

-- preparation for lemma 4
theorem fx_ne_0 : f.eval₂ (algebraMap A B) x ≠ 0 := sorry

theorem residue_primitive_of_add_uniformizer (hx : (ResidueField A)⟮residue B x⟯ = ⊤) : (ResidueField A)⟮residue B (x + ϖ)⟯ = ⊤ := sorry

/-
this is part of lemma 4:
If `f x` has valuation ≥ 2, then `f (x + ϖ)` is a uniformizer.
-/
theorem lemma4_val_ge_2 (h_fx : ¬Irreducible (f.eval₂ (algebraMap A B) x)) : Irreducible (f.eval₂ (algebraMap A B) (x + ϖ)) := sorry

/-
The following two theorem states that `B = A[x]` if `f x` is a uniformizer;
otherwise `B = A[x + ϖ]`.
However, this does not imply that `B` has a finite `A`-basis.
Should use `lemma3_weak'` to prove.
-/
-- theorem thm_val_1' (h_fx : Irreducible (f.eval₂ (algebraMap A B) x)) : Algebra.adjoin A {x} = ⊤ := sorry
-- theorem thm_val_ge_2 (h_fx : ¬Irreducible (f.eval₂ (algebraMap A B) x)) : Algebra.adjoin A {x + ϖ} = ⊤ := sorry

end x_and_f

/-`B = A[x]` if `k_B = k_A[x]` AND `f x` is a uniformizer.
Should use `lemma3_weak'` to prove.-/
theorem thm_val_1 {x : B} (hx : (ResidueField A)⟮residue B x⟯ = ⊤)
    {f : A[X]} (h_fx : Irreducible (f.eval₂ (algebraMap A B) x)) :
  Algebra.adjoin A {x} = ⊤ := sorry

variable (A) (B)

theorem exists_primitive : ∃x : B, Algebra.adjoin A {x} = ⊤ := by
  rcases exists_x A B with ⟨x, hx⟩
  rcases exists_f_of_x A B x with ⟨f, _, _⟩
  exact if h : Irreducible (eval₂ (algebraMap A B) x f)
    then ⟨x, (thm_val_1 hx h)⟩
    else ⟨x + (DiscreteValuationRing.exists_irreducible B).choose, (thm_val_1 (residue_primitive_of_add_uniformizer hx) (lemma4_val_ge_2 h))⟩

/-
WARNING: possible inst conflict
move higher?
-/
variable [NoZeroSMulDivisors A B]


def PowerBasisExtDVR : PowerBasis A B :=
  (Algebra.adjoin.powerBasis' (IsIntegral.of_finite _ _)).map
    (AlgEquiv.ofTop (choose_spec (exists_primitive _ _)))


end ExtDVR