import RamificationGroup.Valued.Defs

/-!
# Extension of Valuation

In this file, we define the typeclass for valuation extensions and prove basic facts about
extension of valuations.

## Main Definition

* `IsValExtension R A` : The valuation on `A` is an extension of the valuation on `R`.

## References

-/
open Valued Valuation

namespace Valued

variable {R S : Type*} {ΓR ΓS : outParam Type*} [Ring R] [Ring S]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS]
  [vR : Valued R ΓR] [vS : Valued S ΓS] {f : R →+* S} (hf : vR.v.IsEquiv <| vS.v.comap f)

@[simp]
theorem val_map_le_iff (x y : R) : v (f x) ≤ v (f y) ↔ v x ≤ v y :=
  (hf x y).symm

@[simp]
theorem val_map_lt_iff (x y : R) : v (f x) < v (f y) ↔ v x < v y := by
  convert (val_map_le_iff hf y x).not <;>
  push_neg <;> rfl

@[simp]
theorem val_map_le_one_iff (x : R) : v (f x) ≤ 1 ↔ v x ≤ 1 := by
  convert val_map_le_iff hf x 1 <;>
  simp only [_root_.map_one]

@[simp]
theorem val_map_lt_one_iff (x : R) : v (f x) < 1 ↔ v x < 1 := by
  convert val_map_lt_iff hf x 1 <;>
  simp only [_root_.map_one]

end Valued

-- is injectivity needed here?
/--
An instance of `IsValExtension R A` states that the valuation of `A` is an extension of the valuation on `R`.
-/
class IsValExtension (R A : Type*) {ΓR ΓA : outParam Type*} [CommRing R] [Ring A]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA]
  [Algebra R A] [vR : Valued R ΓR] [vA : Valued A ΓA] : Prop where
  /-- the valuation on `R` is equivlent to the comap of the valuation on `A` -/
  val_isEquiv_comap : vR.v.IsEquiv <| vA.v.comap (algebraMap R A)

namespace IsValExtension

section

variable {R A : Type*} {ΓR ΓA : outParam Type*} [CommRing R] [Ring A]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA]
  [Algebra R A] [vR : Valued R ΓR] [vA : Valued A ΓA] [IsValExtension R A]

@[simp, norm_cast]
theorem val_map_le_iff (x y : R) : v (algebraMap R A x) ≤ v (algebraMap R A y) ↔ v x ≤ v y :=
  Valued.val_map_le_iff val_isEquiv_comap x y

@[simp, norm_cast]
theorem val_map_lt_iff (x y : R) : v (algebraMap R A x) < v (algebraMap R A y) ↔ v x < v y :=
  Valued.val_map_lt_iff val_isEquiv_comap x y

@[simp, norm_cast]
theorem val_map_le_one_iff (x : R) : v (algebraMap R A x) ≤ 1 ↔ v x ≤ 1 :=
  Valued.val_map_le_one_iff val_isEquiv_comap x

@[simp, norm_cast]
theorem val_map_lt_one_iff (x : R) : v (algebraMap R A x) < 1 ↔ v x < 1 :=
  Valued.val_map_lt_one_iff val_isEquiv_comap x

instance id : IsValExtension R R where
  val_isEquiv_comap := by
    simp only [Algebra.id.map_eq_id, comap_id]
    rfl

end

section

variable {R A : Type*} {ΓR ΓA : outParam Type*} [Field R] [Ring A]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA]
  [Algebra R A] [vR : Valued R ΓR] [vA : Valued A ΓA] [IsValExtension R A]

def of_integer_comap {R A : Type*} {ΓR ΓA : outParam Type*} [Field R] [Ring A]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA]
  [Algebra R A] [vR : Valued R ΓR] [vA : Valued A ΓA] [IsValExtension R A] (h : vA.v.integer.comap (algebraMap R A) = vR.v.integer) : IsValExtension R A where
  val_isEquiv_comap := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    rw [← Valuation.mem_integer_iff, ← Valuation.mem_integer_iff]
    rw [← h]
    rfl

def of_valuationSubring_comap {R A : Type*} {ΓR ΓA : outParam Type*} [Field R] [Field A]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA]
  [Algebra R A] [vR : Valued R ΓR] [vA : Valued A ΓA] [IsValExtension R A] (h : 𝒪[A].comap (algebraMap R A) = 𝒪[R]) : IsValExtension R A := by
    apply of_integer_comap
    rw [show vR.v.integer = 𝒪[R].toSubring by rfl, ← h]
    rfl

end

end IsValExtension
