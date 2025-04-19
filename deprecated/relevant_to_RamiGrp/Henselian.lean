import Mathlib.RingTheory.Henselian

variable (R : Type*) [CommRing R]

open LocalRing

-- instance instHenselianLocalToHenselian [l : LocalRing R] [h : HenselianRing R <| maximalIdeal R] :
--   HenselianLocalRing R := {
--     l with
--     is_henselian := by
--       convert h.is_henselian
--       letI : IsLocalHom (Ideal.Quotient.mk (maximalIdeal R)) := by
--         apply LocalRing.instIsLocalRingHomResidueFieldResidue
--       rw [isUnit_map_iff]
--   }
