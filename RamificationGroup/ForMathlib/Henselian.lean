import Mathlib.RingTheory.Henselian

variable (R : Type*) [CommRing R]

open LocalRing

instance instHenselianLocalToHenselian [l : LocalRing R] [h : HenselianRing R <| maximalIdeal R] :
  HenselianLocalRing R := {
    l with
    is_henselian := by
      convert h.is_henselian
      letI : IsLocalRingHom (Ideal.Quotient.mk (maximalIdeal R)) := by
        apply LocalRing.instIsLocalRingHomResidueFieldToSemiringToCommSemiringToSemiringToDivisionSemiringToSemifieldFieldResidue
      rw [isUnit_map_iff]
  }
