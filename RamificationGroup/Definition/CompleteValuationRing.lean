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

/-
-- `Bad Choice, not compatible with CDVF`
class CompleteDiscreteValuationRing (R : Type*) [CommRing R] [IsDomain R] extends DiscreteValuationRing R, CompleteValuationRing R
-/

class CompleteDiscreteValuationRing (R : Type*) [CommRing R] [IsDomain R] extends CompleteValuationRing R where
  is_discrete : sorry

-- these two definition is not so necessary
class CompleteValuationField (R : Type*) [Field R] extends CompleteValuationRing R

class CompleteDiscreteValuationField (R : Type*) [Field R] extends CompleteValuationRing R
