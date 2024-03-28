/-
-/
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.NumberTheory.RamificationInertia
import RamificationGroup.Valuation.SubAlgEquiv
import RamificationGroup.Valuation.PolyTaylor
import LocalClassFieldTheory.DiscreteValuationRing.ResidueField

variable {A : Type*} [CommRing A] [LocalRing A]
variable {B : Type*} [CommRing B] [LocalRing B]
variable [Algebra A B] [is_local : IsLocalRingHom (algebraMap A B)]

open LocalRing Classical

noncomputable

section local_ring

namespace LocalRing

variable (A) (B) in
def ramificationIdx : ℕ := Ideal.ramificationIdx (algebraMap A B) (maximalIdeal A) (maximalIdeal B)

variable (A) (B) in
def inertiaDeg : ℕ := Ideal.inertiaDeg (algebraMap A B) (maximalIdeal A) (maximalIdeal B)

instance instAlgebraResidue : Algebra (ResidueField A) (ResidueField B) :=
  Ideal.Quotient.algebraQuotientOfLEComap <| le_of_eq (((local_hom_TFAE <| algebraMap A B).out 0 4 rfl rfl).mp is_local).symm

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

theorem maximalIdeal_pow_eq_span_irreducible_pow (n : ℕ) : maximalIdeal A ^ n = Ideal.span {ϖ ^ n} := by
  rw [Irreducible.maximalIdeal_eq hϖ, Ideal.span_singleton_pow]

end DiscreteValuationRing

end dvr

namespace ExtDVR

variable [Module.Finite A B] [IsSeparable (ResidueField A) (ResidueField B)]

instance instFiniteExtResidue : FiniteDimensional (ResidueField A) (ResidueField B) := FiniteDimensional_of_finite

open IntermediateField Polynomial Classical DiscreteValuationRing

variable (A) (B) in
/--exists `x : B` generating `k_B` over `k_A` -/
theorem exists_lift_residue_primitive : ∃x : B, (ResidueField A)⟮residue B x⟯ = ⊤ := by
  let x := (Field.exists_primitive_element (ResidueField A) (ResidueField B)).choose
  use (Ideal.Quotient.mk_surjective x).choose
  rw [← (Field.exists_primitive_element (ResidueField A) (ResidueField B)).choose_spec]
  congr
  apply (Ideal.Quotient.mk_surjective x).choose_spec

variable (A) in
/-- For any `x : k_B`, there eixsts `f : A[X]` that reduces to the minimal polynomial of `x` over `k_A` -/
theorem exists_lift_polynomial_of_residue (x : B) : ∃f : A[X], f.map (residue A) = minpoly (ResidueField A) (residue B x) := by
  let f0 := minpoly (ResidueField A) (residue B x)
  have : (Polynomial.map (residue A)).Surjective := map_surjective (residue A) Ideal.Quotient.mk_surjective
  use (this f0).choose
  rw [(this f0).choose_spec]

section x_and_f

open Subalgebra

-- `x` : a lift of a primitive element of `k_B/k_A`
variable {x : B} (hx : (ResidueField A)⟮residue B x⟯ = ⊤)
-- `f` : a polynomial with `A`-coeff that reduces to the minpoly of `x : k_B` over `k_A`
variable {f : A[X]} (h_red : f.map (residue A) = minpoly (ResidueField A) (residue B x))
-- `ϖ` : a uniformizer `ϖ` of `B`
variable {ϖ : B} (hϖ : Irreducible ϖ)

/-- Auxiliary lemma: `A[x, ϖ] ⊔ m_B = ⊤`. Can be strenthened to `A[x] ⊔ m_B = B`-/
lemma adjoin_lift_residue_primitive_and_irreducible_sup_maximalIdeal_eq_top : toSubmodule (Algebra.adjoin A {x, ϖ}) ⊔ (maximalIdeal B).restrictScalars A = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨g0, hg0⟩ : ∃g : (ResidueField A)[X], aeval (residue B x) g = residue B y := by
    rw [← AlgHom.mem_range, ← Algebra.adjoin_singleton_eq_range_aeval,
      ← IntermediateField.adjoin_simple_toSubalgebra_of_integral (IsIntegral.of_finite _ _), hx]
    simp only[top_toSubalgebra, Algebra.mem_top]
  let g : A[X] := (map_surjective (residue A) Ideal.Quotient.mk_surjective g0).choose
  rw [show y = g.eval₂ (algebraMap A B) x + (y - g.eval₂ (algebraMap A B) x) by rw [add_sub_cancel'_right]]
  apply Submodule.add_mem_sup
  · rw [Subalgebra.mem_toSubmodule]
    apply Algebra.adjoin_mono (show ({x} : Set B) ⊆ {x, ϖ} by simp only [Set.singleton_subset_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff, true_or])
    apply aeval_mem_adjoin_singleton
  · rw [Submodule.restrictScalars_mem, ← Ideal.Quotient.eq_zero_iff_mem,
      show Ideal.Quotient.mk (maximalIdeal B) = residue B by rfl,
      map_sub]
    erw [hom_eval₂, algebraMap_residue_compat, ← eval₂_map,
      (map_surjective (residue A) Ideal.Quotient.mk_surjective g0).choose_spec,
      ← aeval_def, hg0, sub_self]

/-- Auxiliary lemma: `A[x, ϖ] ⊔ m_B ^ i = ⊤` for any `i : ℕ`-/
lemma adjoin_lift_residue_primitive_and_irreducible_sup_maximalIdeal_pow_eq_top (i : ℕ) : toSubmodule (Algebra.adjoin A {x, ϖ}) ⊔ (maximalIdeal B ^ i).restrictScalars A = ⊤ := by
  induction' i with i hi
  · simp only [Nat.zero_eq, pow_zero, Ideal.one_eq_top, Submodule.restrictScalars_top, ge_iff_le,
    le_top, sup_of_le_right]
  · rw [eq_top_iff, ← hi]
    intro y hy
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy
    obtain ⟨c, hc⟩ : ∃c : B, b = ϖ ^ i * c := by
      rw [maximalIdeal_pow_eq_span_irreducible_pow hϖ, Submodule.restrictScalars_mem, Ideal.mem_span_singleton'] at hb
      rcases hb with ⟨c, hc⟩
      use c
      rw [← hc, mul_comm]
    have : c ∈ toSubmodule (Algebra.adjoin A {x, ϖ}) ⊔ (maximalIdeal B).restrictScalars A := by
      rw [adjoin_lift_residue_primitive_and_irreducible_sup_maximalIdeal_eq_top hx]
      apply Submodule.mem_top
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp this
    obtain ⟨w, hw⟩ : ∃w : B, v = ϖ * w := by
      rw [Irreducible.maximalIdeal_eq hϖ, Submodule.restrictScalars_mem, Ideal.mem_span_singleton'] at hv
      rcases hv with ⟨c, hc⟩
      use c
      rw [← hc, mul_comm]
    rw [← hab, hc, ← huv, mul_add, ← add_assoc, hw, ← mul_assoc]
    apply Submodule.add_mem_sup
    · apply Submodule.add_mem
      · assumption
      · rw [Subalgebra.mem_toSubmodule]
        apply mul_mem
        · apply Algebra.adjoin_mono (show ({ϖ} : Set B) ⊆ {x, ϖ} by simp only [Set.subset_insert])
          apply Algebra.pow_mem_adjoin_singleton
        · assumption
    · rw [Submodule.restrictScalars_mem, maximalIdeal_pow_eq_span_irreducible_pow hϖ, Ideal.mem_span_singleton']
      use w
      rw [mul_comm, pow_succ, mul_comm ϖ]

/-- `m_A • B ≠ ⊥` -/
theorem maximalIdeal_map_ne_bot_of_injective (h_inj : Function.Injective (algebraMap A B)) : (maximalIdeal A).map (algebraMap A B) ≠ ⊥ := by
  intro h
  rw [Ideal.map_eq_bot_iff_of_injective h_inj] at h
  apply DiscreteValuationRing.not_a_field' (R := A) h

/--
lemma 3 states that `xⁱϖʲ`'s with finite many `i j`'s form a `A`-basis of `B`.
This is an alternative and weaker version of lemma 3,
stating that `A[x, ϖ] = B`.
-/
theorem adjoin_lift_residue_primitive_and_irreducible_eq_top (h_inj : Function.Injective (algebraMap A B)) : Algebra.adjoin A {x, ϖ} = ⊤ := by
  rw [← Algebra.toSubmodule_eq_top, eq_top_iff]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot _ (le_of_eq (jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm) -- Nakayama's lemma
  · rw [Ideal.smul_top_eq_map]
    obtain ⟨n, hn⟩ : ∃n : ℕ, (maximalIdeal A).map (algebraMap A B) = maximalIdeal B ^ n := by
      rcases (TFAE B (not_isField B)).out 0 6 with ⟨h, _⟩
      apply h; assumption
      apply maximalIdeal_map_ne_bot_of_injective h_inj
    rw [hn, adjoin_lift_residue_primitive_and_irreducible_sup_maximalIdeal_pow_eq_top hx hϖ]
  · apply Module.finite_def.mp
    assumption

-- preparation for lemma 4
theorem residue_primitive_of_add_uniformizer (hx : (ResidueField A)⟮residue B x⟯ = ⊤) : (ResidueField A)⟮residue B (x + ϖ)⟯ = ⊤ := by
  rw [← residue_eq_add_irreducible hϖ]
  exact hx

theorem not_unit_aeval_lift_residue_primitive : ¬IsUnit (f.eval₂ (algebraMap A B) x) := by
  rw [is_unit_iff_residue_ne_zero, ne_eq, not_not,
    hom_eval₂, algebraMap_residue_compat, ← eval₂_map,
    ← aeval_def, h_red, minpoly.aeval]

/--
This is the first part of lemma 4:
If `f x` has valuation ≥ 2, then `f (x + ϖ)` is a uniformizer.
-/
theorem irreducible_aeval_lift_redisue_primitive_add_irreducible_of_reducible_aeval_lift_residue_primitve (h_fx : ¬Irreducible (f.eval₂ (algebraMap A B) x)) : Irreducible (f.eval₂ (algebraMap A B) (x + ϖ)) := by
  obtain ⟨b, hb⟩ := taylor_order_one_apply₂ f (algebraMap A B) x ϖ
  obtain ⟨y, hy⟩ := mul_irreducible_square_of_not_unit_of_not_irreducible hϖ h_fx (not_unit_aeval_lift_residue_primitive h_red)
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

/--
This is the second part of lemma 4:
`B = A[x]` if `k_B = k_A[x]` and `f x` is a uniformizer.-/
theorem adjoin_lift_primitive_eq_top_of_irreducible_aeval_lift_residue_primitive (h_inj : Function.Injective (algebraMap A B)) {x : B} (hx : (ResidueField A)⟮residue B x⟯ = ⊤)
    {f : A[X]} (h_fx : Irreducible (f.eval₂ (algebraMap A B) x)) :
    Algebra.adjoin A {x} = ⊤ := by
  apply Algebra.adjoin_eq_of_le
  · simp only [Algebra.coe_top, Set.subset_univ]
  let fx := f.eval₂ (algebraMap A B) x
  rw [← adjoin_lift_residue_primitive_and_irreducible_eq_top hx h_fx h_inj]
  rw [show ({x, fx} : Set B) = {x} ∪ {fx} by rfl, Algebra.adjoin_union]
  simp only [sup_le_iff, le_refl, true_and, ge_iff_le]
  rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
  apply aeval_mem_adjoin_singleton


variable (A) (B)

/-- For a finite extension of DVR `A ↪ B` with seperable residue field extension,
there exists `x : B` s.t. `B = A[x]`-/
theorem exists_primitive (h_inj : Function.Injective (algebraMap A B)) : ∃x : B, Algebra.adjoin A {x} = ⊤ := by
  rcases exists_lift_residue_primitive A B with ⟨x, hx⟩
  rcases exists_lift_polynomial_of_residue A x with ⟨f, h_red⟩
  exact if h : Irreducible (f.eval₂ (algebraMap A B) x)
    then ⟨x, (adjoin_lift_primitive_eq_top_of_irreducible_aeval_lift_residue_primitive h_inj hx h)⟩
    else ⟨x + (DiscreteValuationRing.exists_irreducible B).choose,
      (adjoin_lift_primitive_eq_top_of_irreducible_aeval_lift_residue_primitive h_inj (residue_primitive_of_add_uniformizer (DiscreteValuationRing.exists_irreducible B).choose_spec hx)
        (irreducible_aeval_lift_redisue_primitive_add_irreducible_of_reducible_aeval_lift_residue_primitve h_red (DiscreteValuationRing.exists_irreducible B).choose_spec h))⟩

variable [NoZeroSMulDivisors A B] -- cannot be inferred if `A → B` is not injective

/-- A power basis of finite extension of DVR `A ↪ B` with seperable residue field extension.-/
noncomputable def PowerBasisExtDVR (h : Function.Injective (algebraMap A B)) : PowerBasis A B :=
  (Algebra.adjoin.powerBasis' (IsIntegral.of_finite _ _)).map
    (AlgEquiv.ofTop (exists_primitive _ _ h).choose_spec)


end ExtDVR
