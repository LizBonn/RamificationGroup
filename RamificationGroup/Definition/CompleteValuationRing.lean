import RamificationGroup.Definition.MissingPiecesOfMathlib
/-!
# Complete Valuation Ring and Complete Discrete Valuation Ring

In this file, we define
-/

open Classical Uniformity Topology Filter Set
-- noncomputable
-- section

class CompleteValuationRing (R : Type*) [CommRing R] [IsDomain R] extends ValuationRing R, UniformSpace R, CompleteSpace R, TopologicalRing R where
  val_top : sorry

class CompleteDiscreteValuationRing (R : Type*) [CommRing R] [IsDomain R] extends DiscreteValuationRing R, CompleteValuationRing R
