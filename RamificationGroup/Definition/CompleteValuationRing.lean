import RamificationGroup.Definition.MissingPiecesOfMathlib
import Mathlib.RingTheory.Valuation.ValuationSubring
/-!
# Complete Valuation Ring and Complete Discrete Valuation Ring

In this file, we define
-/



open Classical Uniformity Topology Filter Set
open ValuationTopology
-- noncomputable
-- section

-- variable  (R : Type*) [CommRing R] [IsDomain R] [ValuationRing R]

class CompleteValuationRing (R : Type*) [CommRing R] [IsDomain R] extends ValuationRing R, CompleteSpace R, OrderTopology R
-- Note that this definition automatically ensures the topology is induced by valuation by `OrderTopology` and instances of `Order R`, `Topology R` from `ValuationRing R`

--`Maybe not so bad, A CDVF can be defined as the valued field whose valuation ring is a CDVR`
class CompleteDiscreteValuationRing (R : Type*) [CommRing R] [IsDomain R] extends DiscreteValuationRing R, CompleteValuationRing R

-- Or `ValuedField?`
-- Now I believe that the valuation structure on a field is not canonical, so its better to store information of the valuation ring.
-- use `mathcal{O}`?
class CompleteValuedField (K : Type*) [Field K] where
  O : ValuationSubring K
  valuation_subring_is_complete : CompleteValuationRing O

class CompleteDiscreteValuedField (K : Type*) [Field K] extends CompleteValuedField K where
  valuation_subring_is_dvr : DiscreteValuationRing O




/-
class CompleteDiscreteValuationRing (R : Type*) [CommRing R] [IsDomain R] extends CompleteValuationRing R where
  is_discrete : sorry

-- Maybe these two definition is not so necessary
class CompleteValuationField (R : Type*) [Field R] extends CompleteValuationRing R

class CompleteDiscreteValuationField (R : Type*) [Field R] extends CompleteValuationRing R
-/
