import RamificationGroup.Valued.RamificationIndex

open DiscreteValuation Valued

variable {K L} [Field K] [Field L] [DiscretelyValued K] [DiscretelyValued L] [ValAlgebra K L] [FiniteDimensional K L]

def ValAlgIso.index (s : L ≃ₐv[K] L) : WithTop ℕ := sorry

def ramificationGroup (i : ℕ) : Subgroup (L ≃ₐv[K] L) := sorry


/-

notation:max " i[" vL:max "/" vK:max "]" => lowerIndex vK vL

notation:max " G(" vL:max "/" vK:max ")_[" n:max "] " => RamificationGroup vK vL n


#check i[vL/vK]
#check G(vL/vK)_[1]



-- Many properties
-- `i <=1, = ⊤` `the filtration is complete`

-- currently there is no subgroup filtration, only ideal filtration, maybe to define it is useful.
-- `the filtration is decreasing, and seperable`

end

section

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (K' : IntermediateField K L) [IsGalois K L] (vK : Valuation K ℤₘ₀) (vK' : Valuation K' ℤₘ₀) (vL : Valuation L ℤₘ₀) [ValuationExtension vK vL] [ValuationExtension vK' vL] --some more condition

-- `key theorem : lower numbering is compatible with subgroup` restate this into a better form...
theorem lower_numbering_inf (i : ℤ) : ((G(vL/vK)_[i]).subgroupOf K'.fixingSubgroup ).map (IntermediateField.fixingSubgroupEquiv K') = G(vL/vK')_[i] := sorry

theorem index_subgroup (s : K'.fixingSubgroup) : i[vL/vK'] (K'.fixingSubgroupEquiv s)  = i[vL/vK] s := sorry


variable [Normal K K'] [ValuationExtension vK vK'] --this should be later changed in to a scalar-tower-like instance
variable [FiniteDimensional K L]
#synth FiniteDimensional K K'
#synth Finite (L ≃ₐ[K] L)
#synth Finite (K' ≃ₐ[K] K')

open BigOperators

-- need instances of computation rules related to WithTop ℤ
instance : Coe (WithTop ℤ) (WithTop ℚ) := sorry
#synth Mul (WithTop ℚ)
theorem index_quotient_group (s₀ : L ≃ₐ[K] L) : i[vK'/vK] (s₀.restrictNormal K')  = ((1 / e(vL/vK) :ℚ) : (WithTop ℚ)) * ∑ s in {s : L ≃ₐ[K] L | s.restrictNormal K' = s₀.restrictNormal K'}.toFinite.toFinset, i[vL/vK] s := sorry
-- do we need to def this index finset separately?

-/
