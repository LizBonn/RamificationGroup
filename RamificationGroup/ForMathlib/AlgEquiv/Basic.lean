import Mathlib.FieldTheory.Normal.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import RamificationGroup.Valued.Hom.Discrete
import Mathlib.RingTheory.Valuation.Discrete.Basic
import RamificationGroup.ForMathlib.Algebra.Algebra.Tower


open DiscreteValuation Valuation Classical AlgHom

variable {K K' L : Type*} {ΓK : outParam Type*} [Field K] [Field K'] [Field L] [Algebra K L] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L]  [Normal K K'] [Normal K L] [FiniteDimensional K L]

variable (σ : K' ≃ₐ[K] K')

omit [Normal K L] [FiniteDimensional K L] in
theorem restrictNormal_restrictNormalHom (s : L ≃ₐ[K] L) : s.restrictNormal K' = AlgEquiv.restrictNormalHom K' s := by rfl

theorem preimage_singleton_nonempty {σ : K' ≃ₐ[K] K'} : ((AlgEquiv.restrictNormalHom K' (K₁ := L))⁻¹' {σ}).toFinset.Nonempty := by
  apply Finset.coe_nonempty.mp
  simp only [Set.coe_toFinset]
  exact Set.Nonempty.preimage (Set.singleton_nonempty _) (AlgEquiv.restrictNormalHom_surjective (F := K) (E := L) (K₁ := K'))

omit [Normal K L] [FiniteDimensional K L] in
theorem AlgEquiv.restrictNormalHom_restrictScalarsHom {x : (L ≃ₐ[K'] L)} : AlgEquiv.restrictNormalHom K' (AlgEquiv.restrictScalarsHom K x) = 1 := by
  unfold restrictNormalHom restrictScalarsHom
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.mk'_apply]
  unfold restrictNormal restrictNormal' AlgHom.restrictNormal restrictNormalAux restrictScalars
  ext t
  rw [one_apply]
  simp only [toAlgHom_eq_coe, RingEquiv.toEquiv_eq_coe, AlgHom.coe_coe, coe_mk, EquivLike.coe_coe, coe_ringEquiv, coe_ofBijective, coe_comp, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply]
  have h1 : (ofInjectiveField (IsScalarTower.toAlgHom K K' L)) t = (ofInjectiveField (IsScalarTower.toAlgHom K K' L)).toAlgHom.toRingHom t := rfl
  rw [h1]
  have h2 : ((ofInjectiveField (IsScalarTower.toAlgHom K K' L)).toAlgHom.toRingHom t) = algebraMap K' L t := rfl
  simp only [h2, commutes]
  simp only [← h2, RingHom.coe_coe, Subtype.coe_eta, toAlgHom_eq_coe, toRingHom_eq_coe, toAlgHom_toRingHom, RingHom.coe_coe, symm_apply_apply]

omit [Normal K L] [FiniteDimensional K L] in
theorem AlgEquiv.restrictNormal_ker_eq : (AlgEquiv.restrictNormalHom K').ker = (⊤ : Subgroup (L ≃ₐ[K'] L)).map (AlgEquiv.restrictScalarsHom K) := by
  ext x
  constructor
  · intro hx
    let x' : L ≃ₐ[K'] L := {
      x.toRingEquiv with
      commutes' := by
        intro r
        have h : r = AlgEquiv.restrictNormalHom K' x r := by
          rw [MonoidHom.mem_ker] at hx
          rw [hx, one_apply]
        nth_rw 2 [h]
        rw [AlgEquiv.restrictNormalHom]
        dsimp
        rw [AlgEquiv.restrictNormal_commutes]
    }
    rw [Subgroup.mem_map]
    use x'
    constructor
    · apply Subgroup.mem_top
    · rfl
  · intro hx
    refine (MonoidHom.mem_ker (f := restrictNormalHom K')).mpr ?h.mpr.a
    obtain ⟨t, ht1, ht2⟩ := Subgroup.mem_map.1 hx
    rw [← ht2, AlgEquiv.restrictNormalHom_restrictScalarsHom]
