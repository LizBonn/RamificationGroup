import RamificationGroup.Valued.Hom.Lift
import Mathlib.FieldTheory.Galois

open DiscreteValuation Valued Valuation

section

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [ValAlgebra R S]

def lowerRamificationGroup (i : ℤ) : Subgroup (S ≃ₐv[R] S) where
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

end

section WithBot
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

end WithBot

section lowerIndex

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [ValAlgebra R S]

open Classical
noncomputable def ValAlgEquiv.lowerIndex (s : S ≃ₐv[R] S) : ℕ∞ :=
  if h : iSup (fun x : vS.v.integer => (Valued.v (s.liftInteger x - x))) = 0 then ⊤
  else (- Multiplicative.toAdd (WithZero.unzero h)).toNat

scoped [Valued] notation:max " G(" S:max "/" R:max ")_[" n:max "] " => lowerRamificationGroup R S n

scoped [Valued] notation:max " i_[" S:max "/" R:max "]" => ValAlgEquiv.lowerIndex R S

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

-/

noncomputable def ValAlgEquiv.truncatedLowerIndex (s : (S ≃ₐv[R] S)) (u : ℚ) : ℚ :=
  if h : i_[S/R] s = ⊤ then u
  else if u ≤ (i_[S/R] s).untop h then u
  else (i_[S/R] s).untop h

#check ValAlgEquiv.truncatedLowerIndex

end lowerIndex

#check AlgEquiv.restrictScalars

variable {K K' L : Type*} {ΓK ΓK' : outParam Type*} [Field K] [Field K'] [Field L] [LinearOrderedCommGroupWithZero ΓK]
[LinearOrderedCommGroupWithZero ΓK']
[vK : Valued K ΓK] [vK' : Valued K' ΓK'] [vL : Valued L ℤₘ₀] [ValAlgebra K L] --{H : Subgroup (L ≃ₐ[K] L)} [H.Normal]
[Algebra K K'] [ValAlgebra K' L] [IsScalarTower K K' L]

section

variable (R : Type*) {S A B : Type*} {ΓR ΓS ΓA ΓB : outParam Type*} [CommRing R] [CommRing S] [Ring A] [Ring B]
[LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS]
[LinearOrderedCommGroupWithZero ΓA]
[LinearOrderedCommGroupWithZero ΓB]
[vR : Valued R ΓR] [vS : Valued S ΓS] [vA : Valued A ΓA] [vB : Valued B ΓB]
[Algebra R S] [ValAlgebra R A] [ValAlgebra S A] [ValAlgebra R B] [ValAlgebra S B] [IsScalarTower R S A] [IsScalarTower R S B]

#synth CommSemiring R

def ValAlgEquiv.restrictScalars (f : A ≃ₐv[S] B) : A ≃ₐv[R] B :=
  {
    f.toValRingEquiv, f.toAlgEquiv.restrictScalars R with
  }

def ValAlgEquiv.restrictScalarsₘ : (A ≃ₐv[S] A) →* (A ≃ₐv[R] A) where -- add this bundled version for AlgEquiv.restrictScalars
  toFun := ValAlgEquiv.restrictScalars R
  map_one' := rfl
  map_mul' _ _ := by
    ext
    rfl

#check AlgEquiv.restrictScalars

end

@[simp]
theorem lowerIndex_refl : (i_[L/K] .refl) = ⊤ := by
  simp [ValAlgEquiv.lowerIndex]

@[simp]
theorem truncatedLowerIndex_refl (u : ℚ): ValAlgEquiv.truncatedLowerIndex K L .refl u = u := by
  simp [ValAlgEquiv.truncatedLowerIndex]

@[simp]
theorem lowerIndex_restrictScalars (s : L ≃ₐv[K'] L) : i_[L/K] (s.restrictScalars K) =  i_[L/K'] s := rfl

@[simp]
theorem truncatedLowerIndex_restrictScalars (u : ℚ) (s : L ≃ₐv[K'] L) : (s.restrictScalars K).truncatedLowerIndex K L u = s.truncatedLowerIndex K' L u := rfl

@[simp]
theorem lowerRamificationGroup_restrictScalars (u : ℤ) : G(L/K)_[u].comap (ValAlgEquiv.restrictScalarsₘ K) = G(L/K')_[u] := rfl
