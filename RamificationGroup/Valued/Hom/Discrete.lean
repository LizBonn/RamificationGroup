import RamificationGroup.Valued.Hom.Basic


section

-- `key def : If L/K  a finite field extension of local field, then there exist a extension of valuation`, see Maria and Phillip, `discrete_valuation_ring.extensions`

def DiscretelyValued.extensionFiniteDimension {K} (L) [Field K] [Field L] [DiscretelyValued K] [Algebra K L] [FiniteDimensional K L] : DiscretelyValued L  := sorry

-- instance : Valued L

-- `key theorem: If L/K is a finite field extension + more conditions, then any 2 extension of valuations from K on L are equivalent`; Discrete Valuations are equal
theorem Valuation.isEquiv_of_finiteDimensional {K L : Type*} [Field K] [Field L] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] [vK : DiscretelyValued K] [vL : Valued L Γ] [ValAlgebra K L] [FiniteDimensional K L]
 : vL.v.IsEquiv (vK.extensionFiniteDimension L).v := sorry

-- any alg map preserves valuation, thus we can define a function input alg map output val alg map

-- some Unique instance?


-- Unique instance in the case of Local Fields, which comes from uniqueness of extension of valuation.

end
