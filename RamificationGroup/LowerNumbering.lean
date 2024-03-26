import RamificationGroup.Valued.Hom.Lift
import Mathlib.FieldTheory.Galois

open DiscreteValuation Valued Valuation

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [ValAlgebra R S]

def lowerRamificationGroup (i : ℤ) : (Subgroup (S ≃ₐv[R] S)) where
    carrier := {s | ∀ x : vS.v.integer, Valued.v (s.liftInteger x - x) ≤ .coe (.ofAdd (- i - 1))}
    mul_mem' := sorry
    one_mem' := sorry
    inv_mem' := sorry

theorem lowerRamificationGroup.antitone : Antitone (lowerRamificationGroup R S) := sorry

-- -- Is such a bundled version better? OrderDual can be add at either source or target.
-- def lowerRamificationGroup' : OrderHom ℤᵒᵈ (Subgroup (S ≃ₐv[R] S)) where
--   toFun i := {
--     carrier := {s | ∀ x : vS.v.integer, vS.v (s x - x) ≤ .coe (.ofAdd (- OrderDual.ofDual i - 1)) }
--     mul_mem' := sorry
--     one_mem' := sorry
--     inv_mem' := sorry
--   }
--   monotone' := sorry

-- this should be put into a suitable place, Also add `WithOne`? `WithTop`, `WithBot`, `WithOne`, `Muliplicative`, `Additive`
open Classical

-- there is no `ConditionallyCompleteLinearOrderTop` in mathlib ...
#check WithBot.linearOrder
noncomputable instance {α} [ConditionallyCompleteLinearOrder α] : ConditionallyCompleteLinearOrderBot (WithBot α) where
  toConditionallyCompleteLattice := WithBot.conditionallyCompleteLattice
  le_total := WithBot.linearOrder.le_total
  decidableLE := WithBot.decidableLE
  decidableEq := WithBot.decidableEq
  decidableLT := WithBot.decidableLT
  csSup_of_not_bddAbove s h := by
    by_cases hbot : s ⊆ {⊥}
    · simp [sSup, sInf]
      sorry
    · simp [sSup, sInf]
      intro x hxs hx
      sorry
  csInf_of_not_bddBelow := sorry
  bot_le := WithBot.orderBot.bot_le
  csSup_empty := by simp only [WithBot.csSup_empty]

noncomputable instance {α} [ConditionallyCompleteLinearOrder α] : ConditionallyCompleteLinearOrderBot (WithZero α) := inferInstanceAs (ConditionallyCompleteLinearOrderBot (WithBot α))

instance {α} [Add α] [ConditionallyCompleteLinearOrder α] : ConditionallyCompleteLinearOrder (Multiplicative α) := inferInstanceAs (ConditionallyCompleteLinearOrder α)

#synth Add ENat
#check WithTop.untop
-- instance : ConditionallyCompleteLinearOrderBot ℤₘ₀ := inferInstanceAs (ConditionallyCompleteLinearOrderBot (WithZero ℤ))

open Classical
noncomputable def ValAlgEquiv.lowerIndex (s : S ≃ₐv[R] S) : ℕ∞ :=
  if h : iSup (fun x : vS.v.integer => (Valued.v (s.liftInteger x - x))) = 0 then ⊤
  else (- Multiplicative.toAdd (WithZero.unzero h)).toNat

scoped [DiscreteValuation] notation:max " G(" S:max "/" R:max ")_[" n:max "] " => lowerRamificationGroup R S n

scoped [DiscreteValuation] notation:max " i_[" S:max "/" R:max "]" => ValAlgEquiv.lowerIndex R S

variable (n : ℤ) (s : S ≃ₐv[R] S)
#check G(S/R)_[n]
#check i_[S/R] s

/-
-- Many properties
-- `i <=1, = ⊤` `the filtration is complete`

-- currently there is no subgroup filtration, only ideal filtration, maybe to define it is useful.
-- `the filtration is decreasing, and seperable`

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (K' : IntermediateField K L)
#check K'.isScalarTower_mid'
--#synth IsScalarTower K K' L
--instance : IsScalarTower K K' L := K'.isScalarTower_mid'

variable {K L : Type*} [Field K] [Field L]  [vK : Valued K  ℤₘ₀] [IsDiscrete vK.v] [vL : Valued L ℤₘ₀] [IsDiscrete vL.v] [ValAlgebra K L] (K' : IntermediateField K L) [IsGalois K L] [DiscretelyValued K'] [FiniteDimensional K L] --some more condition

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

noncomputable def ValAlgEquiv.truncatedLowerIndex (s : (S ≃ₐv[R] S)) (u : ℚ): ℚ :=
  if h : i_[S/R] s = ⊤ then u
  else if (i_[S/R] s).untop h > u then u
  else (i_[S/R] s).untop h

#check ValAlgEquiv.truncatedLowerIndex
