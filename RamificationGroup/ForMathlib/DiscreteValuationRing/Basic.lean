import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import RamificationGroup.ForMathlib.LocalRing.Basic

namespace DiscreteValuationRing

open LocalRing

variable {A : Type*} [CommRing A] [IsDomain A] [DiscreteValuationRing A]

section uniformiser

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
    rw [← (irreducible_iff_uniformizer _).mp hϖ, LocalRing.mem_maximalIdeal]
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
  apply LocalRing.is_unit_of_unit_add_nonunit hu
  simp only [mem_nonunits_iff, IsUnit.mul_iff, not_and]
  exact fun _ ↦ Irreducible.not_unit hϖ

theorem maximalIdeal_pow_eq_span_irreducible_pow (n : ℕ) : maximalIdeal A ^ n = Ideal.span {ϖ ^ n} := by
  rw [Irreducible.maximalIdeal_eq hϖ, Ideal.span_singleton_pow]

end uniformiser
