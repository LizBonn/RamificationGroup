import RamificationGroup.Valued.Hom.ValExtension

/-
uniqueness of extension of valuation and the isom between L ≃ₐ[K] L and  L ≃ₐv[K] L

-/
variable {K L} {ΓK ΓL : outParam Type*} [Field K] [Field L] [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]


section
variable [Valued K ΓK] [CompleteSpace K] [Algebra K L]

theorem unique_of_valuation_extension (v₁ v₂ : Valuation L ΓL) (h₁ : v₁.comap (algebraMap K L) = v₂.comap (algebraMap K L)): v₁ = v₂ := sorry

end

-- should be changed G_[-1] = ⊤
/-
section
variable [Valued K ΓK] [CompleteSpace K] [Valued L ΓL] [ValAlgebra K L]

def toValAlgEquiv : (L ≃ₐ[K] L) ≃* (L ≃ₐv[K] L) where
  toFun s := sorry
  invFun := (↑)
  left_inv := _
  right_inv := _
  map_mul' := _

end
-/
