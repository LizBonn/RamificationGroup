import RamificationGroup.Valued.RamificationIndex
import RamificationGroup.Valued.Hom.lift
import Mathlib.FieldTheory.Galois

open DiscreteValuation Valued

namespace ValAlgebra
variable (R S : Type*) {ΓR ΓS : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS] [vR : Valued R ΓR] [vS : Valued S ΓS] [ValAlgebra R S]

def lowerRamificationGroup (γ : ΓS) : Subgroup (S ≃ₐv[R] S) where
  carrier := if γ = 0 then ⊤ else {s : (S ≃ₐv[R] S) | ∀ x : vS.v.integer, vS.v (s x - x) ≤ γ⁻¹}
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

end ValAlgebra

namespace LocalField

end LocalField

variable {R S : Type*} {ΓR ΓS : outParam Type*} [Ring R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS] [Valued R ΓR] [Valued S ΓS]

def ValAlgEquiv.lowerIndex {K L} [Field K] [Field L] [DiscretelyValued K] [DiscretelyValued L] [ValAlgebra K L]
  -- [FiniteDimensional K L] -- is this really needed?
  (s : L ≃ₐv[K] L) : WithTop ℕ := sorry
  -- have require isup to work, Nm0 works but Zm0 failes, restrict to local field cases for now

def lowerRamificationGroup (K L) [Field K] [Field L] [DiscretelyValued K] [vL : DiscretelyValued L] [ValAlgebra K L]
  -- [FiniteDimensional K L] -- is this really needed?
  (i : ℤ) : Subgroup (L ≃ₐv[K] L) where
    carrier := {s | ∀ x : 𝒪[L], vL.v ((s.liftInteger x) - x) ≤ (- i : ℤ) }
    mul_mem' := sorry
    one_mem' := by
      simp
      intro a h
      sorry
    inv_mem' := sorry

-- notation:max " G(" L:max "/" K:max ")_[" n:max "] " => lowerRamificationGroup K L n

/-
-- Many properties
-- `i <=1, = ⊤` `the filtration is complete`

-- currently there is no subgroup filtration, only ideal filtration, maybe to define it is useful.
-- `the filtration is decreasing, and seperable`

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (K' : IntermediateField K L)
#check K'.isScalarTower_mid'
--#synth IsScalarTower K K' L
--instance : IsScalarTower K K' L := K'.isScalarTower_mid'

variable {K L : Type*} [Field K] [Field L]  [DiscretelyValued K] [DiscretelyValued L] [ValAlgebra K L] (K' : IntermediateField K L) [IsGalois K L] [DiscretelyValued K'] [FiniteDimensional K L] --some more condition

--#synth IsScalarTower K K' L

-- should instances of Discretely Valued L, K' auto generated from K? also [ValAlgebra K L]
--instance : ValAlgebra K K' := sorry
--instance : ValAlgebra K' L := sorry
-- `instance IsValScalarTower K K' L`

-- `key theorem : lower numbering is compatible with subgroup` restate this into a better form...
--theorem lower_numbering_inf (i : ℤ) : (((G(L/K)_[i].comap AlgEquiv.toValAlgEquiv.toMonoidHom).subgroupOf K'.fixingSubgroup).map (IntermediateField.fixingSubgroupEquiv K').toMonoidHom).map AlgEquiv.toValAlgEquiv.toMonoidHom = G(L/K')_[i] := sorry

--theorem index_subgroup (s : K'.fixingSubgroup) : i[vL/vK'] (K'.fixingSubgroupEquiv s)  = i[vL/vK] s := sorry


--variable [Normal K K'] [ValuationExtension vK vK'] --this should be later changed in to a scalar-tower-like instance
variable [FiniteDimensional K L]
#synth FiniteDimensional K K'
#synth Finite (L ≃ₐ[K] L)
#synth Finite (K' ≃ₐ[K] K')

open BigOperators

-- need instances of computation rules related to WithTop ℤ
instance : Coe (WithTop ℤ) (WithTop ℚ) := sorry
#synth Mul (WithTop ℚ)
--theorem index_quotient_group (s₀ : L ≃ₐ[K] L) : i[vK'/vK] (s₀.restrictNormal K')  = ((1 / e(vL/vK) :ℚ) : (WithTop ℚ)) * ∑ s in {s : L ≃ₐ[K] L | s.restrictNormal K' = s₀.restrictNormal K'}.toFinite.toFinset, i[vL/vK] s := sorry
-- do we need to def this index finset separately?

-/
