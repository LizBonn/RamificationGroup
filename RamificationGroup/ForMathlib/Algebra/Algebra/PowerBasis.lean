import Mathlib.RingTheory.PowerBasis

open Algebra PowerBasis Polynomial

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
{B : Type*} [Semiring B] [Algebra R B]
{F : Type*} [FunLike F A B] [AlgHomClass F R A B]

theorem Algebra.exists_eq_aeval_generator {s : A} (hgen : adjoin R {s} = ⊤) (x : A) :
  ∃ f : R[X], x = aeval s f := by
  have hx : x ∈ (⊤ : Subalgebra R A) := trivial
  rw [← hgen, adjoin_singleton_eq_range_aeval] at hx
  rcases hx with ⟨p, hp⟩
  exact ⟨p, hp.symm⟩

theorem Algebra.algHomClass_ext_generator {s : A} (hgen : adjoin R {s} = ⊤)
  {f g : F} (h : f s = g s) :
    f = g := by
  apply DFunLike.ext
  intro x
  have hx : x ∈ (⊤ : Subalgebra R A) := trivial
  rw [← hgen, adjoin_singleton_eq_range_aeval] at hx
  rcases hx with ⟨p, hp⟩
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hp
  rw [← hp, ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply, h]

theorem PowerBasis.algHom_ext' (pb : PowerBasis R A) {f g : F} (h : f pb.gen = g pb.gen) :
  f = g := Algebra.algHomClass_ext_generator (adjoin_gen_eq_top pb) h
