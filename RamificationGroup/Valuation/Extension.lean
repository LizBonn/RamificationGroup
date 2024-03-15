/-
TODO:
1. (FIRST THING!!!) complete `x_and_f` to determine the necessary conditions
2. prove `instFiniteExtResidue`.
3. prove `exists_f_of_x`

# of WARNINGs : 3

`isUnit_iff_ne_zero` is a bad name for me.

does `Module.finite` implies `FiniteDimensional`?

elim of `∨` ?

-/
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.NumberTheory.RamificationInertia
import RamificationGroup.Valuation.SubAlgEquiv
import RamificationGroup.Valuation.PolyTaylor
import LocalClassFieldTheory.DiscreteValuationRing.Basic

variable {A : Type*} [CommRing A] [LocalRing A]
variable {B : Type*} [CommRing B] [LocalRing B]
variable [Algebra A B] [IsLocalRingHom (algebraMap A B)]

open LocalRing Classical

noncomputable

section local_ring
namespace LocalRing

variable (A) (B) in
def ramificationIdx : ℕ := Ideal.ramificationIdx (algebraMap A B) (maximalIdeal A) (maximalIdeal B)

variable (A) (B) in
def inertiaDeg : ℕ := Ideal.inertiaDeg (algebraMap A B) (maximalIdeal A) (maximalIdeal B)

/- WARNING : `Smul` of this `Algebra` might be incompatible -/
instance instAlgebraResidue: Algebra (ResidueField A) (ResidueField B) := (ResidueField.map (algebraMap A B)).toAlgebra

theorem algebraMap_residue_compat : (residue B).comp (algebraMap A B) = (algebraMap (ResidueField A) (ResidueField B)).comp (residue A) := LocalRing.ResidueField.map_comp_residue (algebraMap A B)

theorem residue_irreducible_eq_zero {ϖ : A} (h : Irreducible ϖ) : residue A ϖ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ((LocalRing.mem_maximalIdeal _).mpr h.not_unit)

theorem is_unit_iff_residue_ne_zero {x : A} : IsUnit x ↔ residue A x ≠ 0 := by
  rw [← isUnit_map_iff (residue A), isUnit_iff_ne_zero]

theorem residue_eq_add_irreducible {x ϖ : A} (h : Irreducible ϖ) : residue A x = residue A (x + ϖ) := by
  rw [RingHom.map_add, self_eq_add_right, residue_irreducible_eq_zero]
  exact h

end LocalRing
end local_ring

variable [IsDomain A] [DiscreteValuationRing A] [IsDomain B] [DiscreteValuationRing B]

section dvr

namespace DiscreteValuationRing

-- BAD NAME, as it doesn't involve `addval`
theorem irreducible_iff_val_eq_one {ϖ : A} : Irreducible ϖ ↔ (addVal A) ϖ = 1 := by
  constructor
  · exact addVal_uniformizer
  · sorry

end DiscreteValuationRing

end dvr

namespace ExtDVR

variable [Module.Finite A B] [IsSeparable (ResidueField A) (ResidueField B)]

instance instFiniteExtResidue : FiniteDimensional (ResidueField A) (ResidueField B) := sorry

open IntermediateField Polynomial Classical

variable (A) (B) in
theorem exists_x : ∃x : B, (ResidueField A)⟮residue B x⟯ = ⊤ := by
  let x := (Field.exists_primitive_element (ResidueField A) (ResidueField B)).choose
  use (Ideal.Quotient.mk_surjective x).choose
  rw [← (Field.exists_primitive_element (ResidueField A) (ResidueField B)).choose_spec]
  congr
  apply (Ideal.Quotient.mk_surjective x).choose_spec

#check IsIntegral.of_finite
#check RingHom.IsIntegralElem (algebraMap A B)
variable (A) (B) in
theorem exists_f_of_x (x : B) : ∃f : A[X], Monic f ∧ f.map (residue A) = minpoly (ResidueField A) (residue B x) := by
  let f0 := minpoly (ResidueField A) (residue B x)
  sorry

section x_and_f

-- `x` : a lift of a primitive element of `k_B/k_A`
variable {x : B} (hx : (ResidueField A)⟮residue B x⟯ = ⊤)
-- `f` : a monic polynomial with `A`-coeff that reduces to the minpoly of `x : k_B` over `k_A`
variable {f : A[X]} (h_monic : Monic f) (h_red : f.map (residue A) = minpoly (ResidueField A) (residue B x))
-- `ϖ` : a uniformizer `ϖ` of `B`
variable {ϖ : B} (hϖ : Irreducible ϖ)

/-some possibly useful thms are listed below-/
#check minpoly.aeval
#check Algebra.adjoin.powerBasis'
#check IsIntegral.of_finite
#check Algebra.adjoin
-- #check IsPrimitiveRoot.adjoinEquivRingOfIntegers
-- #check IsPrimitiveRoot.integralPowerBasis

/-
lemma 3 states that `xⁱϖʲ`'s with finite many `i j`'s form a `A`-basis of `B`.
The next theorem is an alternate and weaker version of lemma 3,
stating that `A[x, ϖ] = B`.
-/
theorem lemma3_weak : Algebra.adjoin A {x, ϖ} = ⊤ := by
  apply Algebra.eq_top_iff.mpr
  intro y
  sorry

-- preparation for lemma 4
theorem residue_primitive_of_add_uniformizer (hx : (ResidueField A)⟮residue B x⟯ = ⊤) : (ResidueField A)⟮residue B (x + ϖ)⟯ = ⊤ := by
  rw [← residue_eq_add_irreducible hϖ]
  exact hx

theorem fx_not_unit : ¬IsUnit (f.eval₂ (algebraMap A B) x) := by
  rw [is_unit_iff_residue_ne_zero, ne_eq, not_not,
    hom_eval₂, algebraMap_residue_compat, ← eval₂_map,
    ← aeval_def, h_red, minpoly.aeval]

/-
this is part of lemma 4:
If `f x` has valuation ≥ 2, then `f (x + ϖ)` is a uniformizer.
-/
theorem lemma4_val_ge_2 (h_fx : ¬Irreducible (f.eval₂ (algebraMap A B) x)) : Irreducible (f.eval₂ (algebraMap A B) (x + ϖ)) := by
  rcases taylor_order_one_apply₂ f (algebraMap A B) x ϖ with ⟨b, exp⟩
  have : IsUnit ((derivative f).eval₂ (algebraMap A B) x) := by
    apply LocalRing.is_unit_iff_residue_ne_zero.mpr
    sorry
  sorry

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
Should use `lemma3_weak` to prove.-/
theorem thm_val_1 {x : B} (hx : (ResidueField A)⟮residue B x⟯ = ⊤)
    {f : A[X]} (h_fx : Irreducible (f.eval₂ (algebraMap A B) x)) :
    Algebra.adjoin A {x} = ⊤ := by
  sorry

variable (A) (B)

theorem exists_primitive : ∃x : B, Algebra.adjoin A {x} = ⊤ := by
  rcases exists_x A B with ⟨x, hx⟩
  rcases exists_f_of_x A B x with ⟨f, _, _⟩
  exact if h : Irreducible (f.eval₂ (algebraMap A B) x)
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
