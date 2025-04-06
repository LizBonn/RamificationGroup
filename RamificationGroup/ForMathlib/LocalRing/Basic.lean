import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.NumberTheory.RamificationInertia.Basic

namespace IsLocalRing

variable (A B : Type*) [CommRing A] [CommRing B]
  [IsLocalRing A] [IsLocalRing B] [Algebra A B] [is_local : IsLocalHom (algebraMap A B)]

noncomputable def ramificationIdx : ℕ := Ideal.ramificationIdx (algebraMap A B) (maximalIdeal A) (maximalIdeal B)

noncomputable def inertiaDeg : ℕ := Ideal.inertiaDeg (maximalIdeal A) (maximalIdeal B)

instance : Algebra (ResidueField A) (ResidueField B) :=
  Ideal.Quotient.algebraQuotientOfLEComap <| le_of_eq (((local_hom_TFAE <| algebraMap A B).out 0 4 rfl rfl).mp is_local).symm

variable {A B}

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

theorem maximalIdeal_eq_jacobson_of_bot : maximalIdeal A ≤ Ideal.jacobson ⊥ := le_of_eq (jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm

variable (A) in
theorem maximalIdeal_ne_top : maximalIdeal A ≠ ⊤ :=
  Ideal.IsMaximal.ne_top (IsLocalRing.maximalIdeal.isMaximal A)
