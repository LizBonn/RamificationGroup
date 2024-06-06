import RamificationGroup.Valued.Hom.Discrete
import RamificationGroup.DecompositionGroup


open DiscreteValuation Valued Valuation

section hom_eq_iff_integer

variable {R K L : Type*} {ΓK ΓL : outParam Type*} [CommRing R] [Field K] [Field L]
[LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL] [vK : Valued K ΓK] [vL : Valued L ΓL]
[Algebra R K] [Algebra R L]

variable {F : Type*} [FunLike F K L] [MonoidWithZeroHomClass F K L]

namespace Valued

theorem ringHomClass_eq_iff_valuationSubring (f g : F) :
  f = g ↔ ∀ x : 𝒪[K], f x = g x := by
  constructor <;> intro heq
  · simp only [heq, Subtype.forall, mem_valuationSubring_iff, implies_true, forall_const]
  · apply DFunLike.ext
    intro x
    rcases ValuationSubring.mem_or_inv_mem 𝒪[K] x with h | h
    · exact heq ⟨x, h⟩
    · calc
        _ = (f x⁻¹)⁻¹ := by
          simp only [map_inv₀, inv_inv]
        _ = (g x⁻¹)⁻¹ := by
          rw [inv_inj]
          exact heq ⟨x⁻¹, h⟩
        _ = g x := by
          simp only [map_inv₀, inv_inv]


end Valued

end hom_eq_iff_integer

section lift

namespace Valued

section integer

variable {R S : Type*} {ΓR ΓS : outParam Type*} [Ring R] [Ring S]
[LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR][LinearOrderedCommGroupWithZero ΓS] [vS : Valued S ΓS]


def RingHom.restrictInteger {f : R →+* S} (hf : vR.v.IsEquiv (vS.v.comap f)) : vR.v.integer →+* vS.v.integer where
  toFun := by
    refine fun ⟨x, hx⟩ ↦ ⟨f x, ?_⟩
    rw [mem_integer_iff, val_map_le_one_iff (f := f) hf]
    exact hx
  map_one' := by simp only [_root_.map_one, Submonoid.mk_eq_one]
  map_mul' := by simp only [_root_.map_mul, Submonoid.mk_mul_mk, Subtype.forall, implies_true, forall_const]
  map_zero' := by simp only [_root_.map_zero]; rfl
  map_add' := by simp only [_root_.map_add, AddMemClass.mk_add_mk, Subtype.forall, implies_true, forall_const]

@[simp]
theorem RingHom.restrictInteger_apply {f : R →+* S} (hf : vR.v.IsEquiv (vS.v.comap f)) (x : vR.v.integer) : (RingHom.restrictInteger hf x).1 = f x := rfl

end integer

section valuationSubring

variable {R K L : Type*} {ΓK ΓL ΓR: outParam Type*}
[Field R] [Field K] [Field L]
[LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR]
[LinearOrderedCommGroupWithZero ΓK] [vK : Valued K ΓK]
[LinearOrderedCommGroupWithZero ΓL] [vL : Valued L ΓL]
[Algebra R K] [Algebra R L] [IsValExtension R K] [IsValExtension R L]

def RingHom.restrictValuationSubring {f : K →+* L} (hf : vK.v.IsEquiv (vL.v.comap f)) : 𝒪[K] →+* 𝒪[L] := RingHom.restrictInteger hf


@[simp]
theorem RingHom.restrictValuationSubring_apply {f : K →+* L} (hf : vK.v.IsEquiv (vL.v.comap f)) (x : 𝒪[K]) : (RingHom.restrictValuationSubring hf x).1 = f x := rfl

def AlgHom.restrictValuationSubring {f : K →ₐ[R] L} (hf : vK.v.IsEquiv (vL.v.comap f)) : 𝒪[K] →ₐ[𝒪[R]] 𝒪[L] := {
  RingHom.restrictValuationSubring hf with
  commutes' := by
    intro; ext; simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, RingHom.restrictValuationSubring_apply,
      IsValExtension.coe_algebraMap_valuationSubring, RingHom.coe_coe, AlgHom.commutes]
}

@[simp]
theorem AlgHom.restrictValuationSubring_apply {f : K →ₐ[R] L} (hf : vK.v.IsEquiv (vL.v.comap f)) (x : 𝒪[K]) : (AlgHom.restrictValuationSubring hf x).1 = f x := rfl

end valuationSubring

section Galois

section decomposition_grp

variable {K L : Type*} [Field K] [Field L]
{ΓK ΓL : outParam Type*} [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]
[vK : Valued K ΓK] [vL : Valued L ΓL] [Algebra K L] [IsValExtension K L]

variable (s : decompositionGroup K L)

def DecompositionGroup.restrictValuationSubring (s : decompositionGroup K L) :
  𝒪[L] ≃ₐ[𝒪[K]] 𝒪[L] := {
    AlgHom.restrictValuationSubring (f := s.1) (by apply s.2) with
  invFun := (AlgHom.restrictValuationSubring (f := (s⁻¹.1 : L →ₐ[K] L)) (by convert s⁻¹.2))
  left_inv := by
    intro x; ext; simp
    convert AlgEquiv.symm_apply_apply _ _
  right_inv := by
    intro x; ext; simp
    convert AlgEquiv.apply_symm_apply _ _
  }

@[simp]
theorem DecompositionGroup.restrictValuationSubring_apply (s : decompositionGroup K L) (x : 𝒪[L]) :
  (DecompositionGroup.restrictValuationSubring s x).1 = s.1 x := rfl

theorem elem_decompositionGroup_eq_iff_ValuationSubring (s t : decompositionGroup K L) :
  s = t ↔ DecompositionGroup.restrictValuationSubring s = DecompositionGroup.restrictValuationSubring t := by
  rw [Subtype.ext_iff, ringHomClass_eq_iff_valuationSubring, AlgEquiv.ext_iff]
  constructor <;> intro h x
  · ext; simpa only [DecompositionGroup.restrictValuationSubring_apply] using h x
  · simp only [← DecompositionGroup.restrictValuationSubring_apply, h x]

end decomposition_grp

section discrete

variable {K L : Type*} [Field K] [Field L] [vK : Valued K ℤₘ₀] [vL : Valued L ℤₘ₀] [Algebra K L] [FiniteDimensional K L] [IsValExtension K L] [CompleteSpace K] [IsDiscrete vK.v]

def AlgEquiv.restrictValuationSubring (s : L ≃ₐ[K] L) :
  𝒪[L] ≃ₐ[𝒪[K]] 𝒪[L] := DecompositionGroup.restrictValuationSubring ⟨s, by simp only [decompositionGroup_eq_top, Subgroup.mem_top]⟩

@[simp]
theorem AlgEquiv.restrictValuationSubring_apply (s : L ≃ₐ[K] L) (x : 𝒪[L]) :
  (restrictValuationSubring s x).1 = s x := rfl

theorem AlgEquiv.eq_iff_ValuationSubring (s t : L ≃ₐ[K] L) :
  s = t ↔ restrictValuationSubring s = restrictValuationSubring t := by
  unfold AlgEquiv.restrictValuationSubring
  rw [← elem_decompositionGroup_eq_iff_ValuationSubring, Subtype.ext_iff]

end discrete

end Galois


end Valued

end lift
