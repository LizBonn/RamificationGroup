import RamificationGroup.Valued.Hom.ValExtension
import RamificationGroup.ForMathlib.LocalRing.Basic
import RamificationGroup.Valuation.Discrete

/-!
This file is a continuation of the file ValExtension.

We break this file to simplify the import temporarily

-/
open Valuation Valued IsValExtension

section nontrivial

variable {R A : Type*} {ΓR ΓA : outParam Type*} [CommRing R] [Ring A]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA]
  [Algebra R A] [vR : Valued R ΓR] [Nontrivial vR.v] [vA : Valued A ΓA] [h : IsValExtension R A]

variable (R A) in
theorem nontrivial_of_valExtension : Nontrivial vA.v where
  nontrivial := by
    rcases vR.v.nontrivial_def with ⟨r, h0, h1⟩
    use (algebraMap R A) r
    simp only [ne_eq, IsValExtension.val_map_eq_one_iff, h1, not_false_eq_true, and_true]
    rw [show (0 : ΓA) = vA.v (0) from (_root_.map_zero _).symm, show (0 : A) = (algebraMap R A) 0 from (_root_.map_zero _).symm, IsValExtension.val_map_eq_iff]
    simp only [_root_.map_zero, h0, not_false_eq_true]

end nontrivial

section field

variable (K L : Type*) {ΓK ΓL : outParam Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]
    [Algebra K L] [vK : Valued K ΓK] [vL : Valued L ΓL] [IsValExtension K L]

noncomputable def LocalField.ramificationIdx : ℕ :=
  LocalRing.ramificationIdx 𝒪[K] 𝒪[L]

open LocalField

theorem aux2 [FiniteDimensional K L] : ramificationIdx K L ≠ 0 := sorry


#check Ideal.ramificationIdx

end field
