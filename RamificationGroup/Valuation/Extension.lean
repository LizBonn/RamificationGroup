/-
TODO:
1. (FIRST THING!!!) complete `x_and_f` to determine the necessary conditions
2. prove `instFiniteExtResidue`
3. seek a better condition for `f`, then prove `exists_f_of_x`

# of WARNINGs : 1

does `Module.finite` implies `FiniteDimensional`?

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

theorem is_unit_of_unit_add_nonunit {x y : A} (hx : IsUnit x) (hy : y ∈ nonunits A) : IsUnit (x + y) := by
  rw [eq_add_neg_iff_add_eq.mpr (show x + y = x + y by rfl)] at hx
  exact (isUnit_or_isUnit_of_isUnit_add hx).resolve_right fun h ↦ hy ((IsUnit.neg_iff y).mp h)

end LocalRing
end local_ring

variable [IsDomain A] [DiscreteValuationRing A] [IsDomain B] [DiscreteValuationRing B]

section dvr

namespace DiscreteValuationRing

variable {ϖ x : A} (hϖ : Irreducible ϖ)

theorem unit_mul_irreducible_of_irreducible (hx : Irreducible x) : ∃u : A, IsUnit u ∧ x = u * ϖ := by
  obtain ⟨u, hu⟩ : ∃u : A, x = u * ϖ := by
    refine exists_eq_mul_left_of_dvd (addVal_le_iff_dvd.mp ?_)
    apply le_of_eq
    rw [addVal_uniformizer hx, addVal_uniformizer hϖ]
  have : IsUnit u := Or.resolve_right (Irreducible.isUnit_or_isUnit hx hu) hϖ.not_unit
  use u

theorem mul_irreducible_of_not_unit (h : ¬IsUnit x) : ∃y : A, x = y * ϖ := by
  obtain ⟨y, hy⟩ : ∃y : A, y * ϖ = x := by
    apply Ideal.mem_span_singleton'.mp
    rw [← (irreducible_iff_uniformizer _).mp hϖ, mem_maximalIdeal]
    assumption
  use y
  apply Eq.symm hy

theorem mul_irreducible_square_of_not_unit_of_not_irreducible (h1 : ¬Irreducible x) (h2 : ¬IsUnit x) : ∃y : A, x = y * ϖ ^ 2 := by
  obtain ⟨y, hy⟩ := mul_irreducible_of_not_unit hϖ h2
  have : ¬IsUnit y := fun h ↦
    h1 (Eq.mpr (id (congrArg (fun _a ↦ Irreducible _a) hy)) ((irreducible_isUnit_mul h).mpr hϖ))
  obtain ⟨z, hz⟩ := mul_irreducible_of_not_unit hϖ this
  use z
  rw [hy, hz]
  ring

theorem irreducible_of_irreducible_add_addVal_ge_two (hx : Irreducible x) {y : A} : Irreducible (x + y * ϖ ^ 2) := by
  rcases unit_mul_irreducible_of_irreducible hϖ hx with ⟨u, hu, hxu⟩
  rw [hxu, pow_two, ← mul_assoc, ← add_mul]
  apply (irreducible_isUnit_mul _).mpr hϖ
  apply is_unit_of_unit_add_nonunit hu
  simp only [mem_nonunits_iff, IsUnit.mul_iff, not_and]
  exact fun _ ↦ Irreducible.not_unit hϖ

end DiscreteValuationRing

end dvr

namespace ExtDVR

variable [Module.Finite A B] [IsSeparable (ResidueField A) (ResidueField B)]

instance instFiniteExtResidue : FiniteDimensional (ResidueField A) (ResidueField B) := sorry

open IntermediateField Polynomial Classical DiscreteValuationRing

variable (A) (B) in
theorem exists_x : ∃x : B, (ResidueField A)⟮residue B x⟯ = ⊤ := by
  let x := (Field.exists_primitive_element (ResidueField A) (ResidueField B)).choose
  use (Ideal.Quotient.mk_surjective x).choose
  rw [← (Field.exists_primitive_element (ResidueField A) (ResidueField B)).choose_spec]
  congr
  apply (Ideal.Quotient.mk_surjective x).choose_spec

variable (A) (B) in
theorem exists_f_of_x (x : B) : ∃f : A[X], f.map (residue A) = minpoly (ResidueField A) (residue B x) := by
  let f0 := minpoly (ResidueField A) (residue B x)
  have : (Polynomial.map (residue A)).Surjective := map_surjective (residue A) Ideal.Quotient.mk_surjective
  use (this f0).choose
  rw [(this f0).choose_spec]

section x_and_f

-- `x` : a lift of a primitive element of `k_B/k_A`
variable {x : B} (hx : (ResidueField A)⟮residue B x⟯ = ⊤)
-- `f` : a monic polynomial with `A`-coeff that reduces to the minpoly of `x : k_B` over `k_A`
variable {f : A[X]} (h_red : f.map (residue A) = minpoly (ResidueField A) (residue B x))
-- `ϖ` : a uniformizer `ϖ` of `B`
variable {ϖ : B} (hϖ : Irreducible ϖ)

/-some possibly useful thms are listed below-/
#check IsIntegral.of_finite
#check RingHom.IsIntegralElem (algebraMap A B)
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
  -- use Nakayama lemma
  rw [← Algebra.toSubmodule_eq_top]

-- preparation for lemma 4
theorem residue_primitive_of_add_uniformizer (hx : (ResidueField A)⟮residue B x⟯ = ⊤) : (ResidueField A)⟮residue B (x + ϖ)⟯ = ⊤ := by
  rw [← residue_eq_add_irreducible hϖ]
  exact hx

theorem fx_not_unit : ¬IsUnit (f.eval₂ (algebraMap A B) x) := by
  rw [is_unit_iff_residue_ne_zero, ne_eq, not_not,
    hom_eval₂, algebraMap_residue_compat, ← eval₂_map,
    ← aeval_def, h_red, minpoly.aeval]

/--
this is part of lemma 4:
If `f x` has valuation ≥ 2, then `f (x + ϖ)` is a uniformizer.
-/
theorem lemma4_val_ge_2 (h_fx : ¬Irreducible (f.eval₂ (algebraMap A B) x)) : Irreducible (f.eval₂ (algebraMap A B) (x + ϖ)) := by
  obtain ⟨b, hb⟩ := taylor_order_one_apply₂ f (algebraMap A B) x ϖ
  obtain ⟨y, hy⟩ := mul_irreducible_square_of_not_unit_of_not_irreducible hϖ h_fx (fx_not_unit h_red)
  rw [hb, hy, mul_comm ϖ, ← mul_comm b, add_comm, ← add_assoc, ← add_mul, add_comm]
  apply irreducible_of_irreducible_add_addVal_ge_two hϖ
  apply (irreducible_isUnit_mul _).mpr hϖ
  apply LocalRing.is_unit_iff_residue_ne_zero.mpr
  rw [hom_eval₂, algebraMap_residue_compat, ← eval₂_map, ← derivative_map]
  apply Separable.eval₂_derivative_ne_zero
  · rw [h_red]
    apply IsSeparable.separable
  · rw [← aeval_def, h_red, minpoly.aeval]

end x_and_f

/--`B = A[x]` if `k_B = k_A[x]` AND `f x` is a uniformizer.-/
theorem thm_val_1 {x : B} (hx : (ResidueField A)⟮residue B x⟯ = ⊤)
    {f : A[X]} (h_fx : Irreducible (f.eval₂ (algebraMap A B) x)) :
    Algebra.adjoin A {x} = ⊤ := by
  apply Algebra.adjoin_eq_of_le
  · simp only [Algebra.coe_top, Set.subset_univ]
  let fx := f.eval₂ (algebraMap A B) x
  rw [← lemma3_weak (x := x) (ϖ := fx)]
  rw [show ({x, fx} : Set B) = {x} ∪ {fx} by rfl, Algebra.adjoin_union]
  simp only [sup_le_iff, le_refl, true_and, ge_iff_le]
  rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
  apply aeval_mem_adjoin_singleton


variable (A) (B)

theorem exists_primitive : ∃x : B, Algebra.adjoin A {x} = ⊤ := by
  rcases exists_x A B with ⟨x, hx⟩
  rcases exists_f_of_x A B x with ⟨f, h_red⟩
  exact if h : Irreducible (f.eval₂ (algebraMap A B) x)
    then ⟨x, (thm_val_1 hx h)⟩
    else ⟨x + (DiscreteValuationRing.exists_irreducible B).choose,
      (thm_val_1 (residue_primitive_of_add_uniformizer (DiscreteValuationRing.exists_irreducible B).choose_spec hx)
        (lemma4_val_ge_2 h_red (DiscreteValuationRing.exists_irreducible B).choose_spec h))⟩

variable [NoZeroSMulDivisors A B] -- cannot be inferred if `A → B` is not injective

noncomputable def PowerBasisExtDVR : PowerBasis A B :=
  (Algebra.adjoin.powerBasis' (IsIntegral.of_finite _ _)).map
    (AlgEquiv.ofTop (exists_primitive _ _).choose_spec)


end ExtDVR
