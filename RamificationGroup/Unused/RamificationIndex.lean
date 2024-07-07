import RamificationGroup.Valued.Defs
import RamificationGroup.Valued.Hom.Basic
import RamificationGroup.Valued.Hom.Discrete
import RamificationGroup.LowerNumbering

open DiscreteValuation Valuation Valued

namespace ValRingHom

variable {R S : Type*} {ΓR ΓS : outParam Type*} [Ring R] [Ring S] [DiscretelyValued R] [DiscretelyValued S]

def ramificationIndex {R S : Type*} {ΓR ΓS : outParam Type*} [Ring R] [Ring S] [DiscretelyValued R] [DiscretelyValued S] (f : ValRingHom R S) : ℕ := sorry -- min of .v (image of elements of R that has val > 1 in S)
-- `ℕ, not WithTop ℕ`

variable {K K' L : Type*} {ΓK ΓK' : outParam Type*} [CommRing K] [Field K'] [Field L] [LinearOrderedCommGroupWithZero ΓK]
[LinearOrderedCommGroupWithZero ΓK'] [vL : Valued L ℤₘ₀] [Algebra K L]
[Algebra K K'] [Algebra K' L] [IsScalarTower K K' L]

/-- `h` should be `𝒪[L] is finite over 𝒪[K]`-/
theorem lowerIndex_ne_refl_of_FG (h : sorry) {s : L ≃ₐ[K] L} (hs : s ≠ .refl) : i_[L/K] s ≠ ⊤ := by
  intro heq
  simp only [AlgEquiv.lowerIndex, AddSubgroupClass.coe_sub,
    dite_eq_left_iff, ENat.coe_ne_top, imp_false, not_not] at heq
  have : ∀ x : vL.v.integer, v (s x - x) = 0 := sorry
  apply hs; ext x
  rw [AlgEquiv.coe_refl, id_eq, ← sub_eq_zero, ← Valuation.zero_iff vL.v]
  rcases ValuationSubring.mem_or_inv_mem 𝒪[L] x with h | h
  sorry; sorry


-- properties of ramification index, multiplicativity
