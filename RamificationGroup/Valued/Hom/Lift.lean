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


def ringHomToInteger {f : R →+* S} (hf : vR.v.IsEquiv (vS.v.comap f)) : vR.v.integer →+* vS.v.integer where
  toFun := by
    refine fun ⟨x, hx⟩ ↦ ⟨f x, ?_⟩
    rw [mem_integer_iff, val_map_le_one_iff (f := f) hf]
    exact hx
  map_one' := by simp only [_root_.map_one, Submonoid.mk_eq_one]
  map_mul' := by simp only [_root_.map_mul, Submonoid.mk_mul_mk, Subtype.forall, implies_true, forall_const]
  map_zero' := by simp only [_root_.map_zero]; rfl
  map_add' := by simp only [_root_.map_add, AddMemClass.mk_add_mk, Subtype.forall, implies_true, forall_const]

@[simp]
theorem ringHomToInteger_apply {f : R →+* S} (hf : vR.v.IsEquiv (vS.v.comap f)) (x : vR.v.integer) : (ringHomToInteger hf x).1 = f x := rfl

end integer

section valuationSubring

variable {R K L : Type*} {ΓK ΓL ΓR: outParam Type*}
[Field R] [Field K] [Field L]
[LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR]
[LinearOrderedCommGroupWithZero ΓK] [vK : Valued K ΓK]
[LinearOrderedCommGroupWithZero ΓL] [vL : Valued L ΓL]
[Algebra R K] [Algebra R L] [IsValExtension R K] [IsValExtension R L]

def ringHomToValuationSubring {f : K →+* L} (hf : vK.v.IsEquiv (vL.v.comap f)) : 𝒪[K] →+* 𝒪[L] := ringHomToInteger hf

@[simp]
theorem ringHomToValuationSubring_apply {f : K →+* L} (hf : vK.v.IsEquiv (vL.v.comap f)) (x : 𝒪[K]) : (ringHomToValuationSubring hf x).1 = f x := rfl

def algHomToValuationSubring {f : K →ₐ[R] L} (hf : vK.v.IsEquiv (vL.v.comap f)) : 𝒪[K] →ₐ[𝒪[R]] 𝒪[L] := {
  ringHomToValuationSubring hf with
  commutes' := by
    intro; ext; simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, ringHomToValuationSubring_apply,
      IsValExtension.coe_algebraMap_valuationSubring, RingHom.coe_coe, AlgHom.commutes]
}

@[simp]
theorem algHomToValuationSubring_apply {f : K →ₐ[R] L} (hf : vK.v.IsEquiv (vL.v.comap f)) (x : 𝒪[K]) : (algHomToValuationSubring hf x).1 = f x := rfl

end valuationSubring

end Valued

section Galois

section decomposition_grp

variable {K L : Type*} [Field K] [Field L]
{ΓK ΓL : outParam Type*} [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]
[vK : Valued K ΓK] [vL : Valued L ΓL] [Algebra K L] [IsValExtension K L]

variable (s : decompositionGroup K L)

def decompositionGroupToValuationSubring (s : decompositionGroup K L) :
  𝒪[L] →ₐ[𝒪[K]] 𝒪[L] := algHomToValuationSubring (f := s.1) s.2

@[simp]
theorem decompositionGroupToValuationSubring_apply (s : decompositionGroup K L) (x : 𝒪[L]) :
  (decompositionGroupToValuationSubring s x).1 = s.1 x := rfl

theorem elem_decompositionGroup_eq_iff_ValuationSubring (s t : decompositionGroup K L) :
  s = t ↔ decompositionGroupToValuationSubring s = decompositionGroupToValuationSubring t := by
  rw [Subtype.ext_iff, ringHomClass_eq_iff_valuationSubring, AlgHom.ext_iff]
  constructor <;> intro h x
  · ext; simpa only [decompositionGroupToValuationSubring_apply] using h x
  · simp only [← decompositionGroupToValuationSubring_apply, h x]

end decomposition_grp

section discrete

variable {K L : Type*} [Field K] [Field L] [vK : Valued K ℤₘ₀] [vL : Valued L ℤₘ₀] [Algebra K L] [FiniteDimensional K L] [IsValExtension K L] [CompleteSpace K]
[IsDiscrete vK.v]

def algEquivToValuationSubring (s : L ≃ₐ[K] L) :
  𝒪[L] →ₐ[𝒪[K]] 𝒪[L] :=
  decompositionGroupToValuationSubring ⟨s, by simp only [decompositionGroup_eq_top, Subgroup.mem_top]⟩

@[simp]
theorem algEquivToValuationSubring_apply (s : L ≃ₐ[K] L) (x : 𝒪[L]) :
  (algEquivToValuationSubring s x).1 = s x := rfl

theorem algEquiv_eq_iff_ValuationSubring (s t : L ≃ₐ[K] L) :
  s = t ↔ algEquivToValuationSubring s = algEquivToValuationSubring t := by
  unfold algEquivToValuationSubring
  rw [← elem_decompositionGroup_eq_iff_ValuationSubring, Subtype.ext_iff]

end discrete


end Galois

end lift
