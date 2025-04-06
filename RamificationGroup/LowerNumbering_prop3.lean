import RamificationGroup.LowerNumbering
import Mathlib.FieldTheory.KrullTopology

#check lowerIndex_of_powerBasis
#check PowerBasisValExtension


open LocalField DiscreteValuation Valued Valuation

variable {K M L : Type*} [Field K] [Field M] [Field L]
[Algebra K L] [Algebra K M] [Algebra M L]
[Normal K L]
[IsScalarTower K M L]
[FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional M L]
[Normal K M]
[vK : Valued K ℤₘ₀] [IsDiscrete vK.v]
[vM : Valued M ℤₘ₀] [IsDiscrete vM.v]
[vL : Valued L ℤₘ₀] [IsDiscrete vL.v]
[IsValExtension vK.v vL.v] [IsValExtension vM.v vL.v] [IsValExtension vK.v vM.v]
[Algebra.IsSeparable K L] [Algebra.IsSeparable M L] [Algebra.IsSeparable K M]
[CompleteSpace K] [CompleteSpace M]

variable (σ : M ≃ₐ[K] M) (s : L ≃ₐ[K] L)

open AlgEquiv Classical

theorem preimage_nerefl (hsig : σ ≠ .refl) (s : L ≃ₐ[K] L) (hs : s ∈ ((restrictNormalHom M)⁻¹' {σ})) : s ≠ .refl := by
  by_contra hc
  have h : (restrictNormalHom M) (.refl (A₁ := L)) = .refl (R := K) := (restrictNormalHom M).map_one
  simp only [Set.mem_preimage, Set.mem_singleton_iff, hc, h] at hs
  absurd hsig
  exact id (Eq.symm hs)

theorem val_mappb_sub_self_toAdd_nonpos {s : L ≃ₐ[K] L} (hs : s ≠ .refl) (x : PowerBasis 𝒪[K] 𝒪[L]) : 0 ≤ -Multiplicative.toAdd (WithZero.unzero (val_map_powerBasis_sub_ne_zero x hs)) := by
  rw [← toAdd_one, ← toAdd_inv]
  apply Multiplicative.toAdd_le.2
  apply one_le_inv'.mpr
  rw [← WithZero.coe_le_coe]
  simp only [WithZero.coe_unzero, WithZero.coe_one]
  apply val_map_sub_le_one _ x.gen
  exact mem_decompositionGroup s

def WithZero.some {α : Type*} : α → WithZero α :=
  Option.some

def WithZero.MulHom {α : Type*} [Monoid α] : α →* WithZero α where
  toFun := WithZero.some
  map_one' := rfl
  map_mul' _ _ := rfl


theorem WithZero.coe_prod {α β : Type*} [CommMonoid β] {s : Finset α} {f : α → β} : (↑(∏ x ∈ s, f x) : WithZero β) =  (∏ x ∈ s, ↑(f x : WithZero β)) := by
  simp only [WithZero.coe]
  apply map_prod WithZero.MulHom f s

theorem algebraMap_valuationSubring {x : M} (hx : x ∈ vM.v.valuationSubring) : (algebraMap M L x) ∈ vL.v.valuationSubring := (mem_valuationSubring_iff v ((algebraMap M L) x)).mpr ((IsValExtension.val_map_le_one_iff vM.v vL.v x).mpr hx)

theorem algebraMap_valuationSubring_ne_zero {x : M} (hx1 : x ∈ vM.v.valuationSubring) (hx2 : (⟨x, hx1⟩ : vM.v.valuationSubring) ≠ 0) : (⟨algebraMap M L x, algebraMap_valuationSubring hx1⟩ : vL.v.valuationSubring) ≠ 0 := by
  apply Subtype.coe_ne_coe.1
  simp only [ZeroMemClass.coe_zero, ne_eq, map_eq_zero]
  apply Subtype.coe_ne_coe.2 hx2

theorem IsDiscreteValuationRing.irreducible_of_uniformizer' (π : vL.v.valuationSubring) (hpi : vL.v.IsUniformizer π) : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2  (DiscreteValuation.isUniformizer_is_generator v hpi)

theorem sSup_eq_aux (n : ℕ) : sSup {n1 | n1 ≤ n} = n := by
  apply le_antisymm
  · exact csSup_le' fun ⦃a⦄ a ↦ a
  · apply le_csSup
    use n
    unfold upperBounds
    simp only [Set.mem_setOf_eq, imp_self, implies_true]
    simp only [Set.mem_setOf_eq, le_refl]

theorem DiscreteValuationRing.uniformizer_dvd_iff_le {n1 n2 : ℕ} {π : vL.v.valuationSubring} (hpi : vL.v.IsUniformizer π) : π ^ n1 ∣ π ^ n2 ↔ n1 ≤ n2 := by
  constructor <;> intro h
  · have hnezero : π ≠ 0 := by
      apply_mod_cast uniformizer_ne_zero ⟨π, hpi⟩
    have hneunit : ¬ IsUnit π := by
      apply isUniformizer_not_isUnit hpi
    apply (pow_dvd_pow_iff hnezero hneunit).1
    obtain ⟨u1, hu1⟩ := h
    use u1
  · apply pow_dvd_pow
    exact h

theorem ramificationIdx_eq_uniformizer_pow {n : ℕ}
{u : (vL.v.valuationSubring)ˣ} {πL : vL.v.valuationSubring} (hpiL : vL.v.IsUniformizer πL)
{πM : vM.v.valuationSubring} (hpiM : vM.v.IsUniformizer πM) (hnu : (algebraMap M L) πM = πL ^ n * u) : ramificationIdx M L = n := by
  have hirrL:= IsDiscreteValuationRing.irreducible_of_uniformizer' πL hpiL
  have hirrM:= IsDiscreteValuationRing.irreducible_of_uniformizer' πM hpiM
  unfold ramificationIdx IsLocalRing.ramificationIdx Ideal.ramificationIdx
  rw [_root_.Irreducible.maximalIdeal_eq (ϖ := ⟨πM.1,πM.2⟩), _root_.Irreducible.maximalIdeal_eq (ϖ := ⟨πL.1, πL.2⟩)]
  rw [← IsValExtension.coe_algebraMap_valuationSubring] at hnu
  have hnu' : ((algebraMap ↥𝒪[M] ↥𝒪[L]) πM) = (⟨πL.1, πL.2⟩ : vL.v.integer) ^ n * ⟨u.1, u.1.2⟩  := by
    simp only [← SetLike.coe_eq_coe, IsValExtension.coe_algebraMap_integer, Subtype.coe_eta, Subring.coe_mul, SubmonoidClass.coe_pow]
    exact hnu
  have hspan : Ideal.span {πL ^ n * u.1} = Ideal.span {πL ^ n} := by
    apply Ideal.span_singleton_eq_span_singleton.2
    apply Associated.symm
    use u
  have heq : {n_1 | πL ^ n_1 ∣ πL ^ n} = {n_1 | n_1 ≤ n} := by
    ext t
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
    apply DiscreteValuationRing.uniformizer_dvd_iff_le hpiL
  simp only [Subtype.coe_eta, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, hnu', hspan, Ideal.span_singleton_le_span_singleton, heq]
  apply sSup_eq_aux
  simp only [Subtype.coe_eta]
  exact hirrL
  simp only [Subtype.coe_eta]
  exact hirrM

open IsDiscreteValuationRing

theorem ValuationSubring.inv_coe_eq_coe_inv_aux (u : (vL.v.valuationSubring)ˣ) : u.1.1⁻¹ = (u⁻¹).1.1 := by
  rw [← Units.inv_eq_val_inv]
  apply DivisionMonoid.inv_eq_of_mul u.1.1 u.inv ?_
  exact (Submonoid.mk_eq_one v.valuationSubring.toSubmonoid).mp u.val_inv

theorem Valuation.prolongs_by_ramificationIndex {x : M} (hx1 : x ∈ vM.v.valuationSubring) (hx2 : (⟨x, hx1⟩ : vM.v.valuationSubring) ≠ 0) : vM.v (x) ^ ramificationIdx M L = vL.v (algebraMap M L x) := by
  obtain ⟨πL, hpiL⟩ := exists_isUniformizer_of_isDiscrete vL.v
  obtain ⟨πM, hpiM⟩ := exists_isUniformizer_of_isDiscrete vM.v
  obtain ⟨n1, u1, hnu1⟩ := pow_uniformizer vM.v hx2 ⟨πM, hpiM⟩
  obtain ⟨n2, u2, hnu2⟩ := pow_uniformizer vL.v (algebraMap_valuationSubring_ne_zero hx1 hx2) ⟨πL, hpiL⟩
  have hirrL:= IsDiscreteValuationRing.irreducible_of_uniformizer' πL hpiL
  have hirrM:= IsDiscreteValuationRing.irreducible_of_uniformizer' πM hpiM
  simp only [SubmonoidClass.coe_pow] at hnu1 hnu2
  rw [hnu2, hnu1]
  simp only [_root_.map_mul, _root_.map_pow, val_valuationSubring_unit, mul_one]
  have hr' : (⟨algebraMap M L πM, (algebraMap_valuationSubring πM.2)⟩ : vL.v.valuationSubring) ≠ 0 := by
    simp only [← Subtype.coe_ne_coe ,ZeroMemClass.coe_zero, ne_eq, map_eq_zero]
    exact uniformizer_ne_zero ⟨πM, hpiM⟩
  obtain ⟨n, u, hnu⟩ := pow_uniformizer vL.v hr' ⟨πL,hpiL⟩
  simp only [SubmonoidClass.coe_pow] at hnu
  rw [ramificationIdx_eq_uniformizer_pow hpiL hpiM hnu, hpiM, hpiL, ← pow_mul]
  apply congrArg
  apply_fun (algebraMap M L) at hnu1
  simp only [_root_.map_mul, _root_.map_pow, hnu, hnu2, mul_pow, ← pow_mul, mul_comm, mul_assoc] at hnu1
  rw [mul_comm (πL.1 ^ (n1 * n))] at hnu1
  symm
  let u3 : (vL.v.valuationSubring)ˣ := {
    val := ⟨u.1.1 ^ n1 * (algebraMap M L) u1.1.1, by
      apply ValuationSubring.mul_mem
      · apply pow_mem u.1.2
      · refine (mem_valuationSubring_iff v ((algebraMap M L) ↑↑u1)).mpr ?_
        refine (IsValExtension.val_map_le_one_iff vM.v vL.v u1.1.1).mpr ?_
        apply (mem_valuationSubring_iff v u1.1.1).1 u1.1.2
      ⟩
    inv := ⟨(algebraMap M L) u1.1.1⁻¹ * u.1.1⁻¹ ^ n1, by
      apply ValuationSubring.mul_mem
      · apply algebraMap_valuationSubring
        have hu := u1.2.2
        rw [Units.inv_eq_val_inv] at hu
        rw [ValuationSubring.inv_coe_eq_coe_inv_aux]
        exact hu
      · apply pow_mem
        have hu := u.2.2
        rw [Units.inv_eq_val_inv] at hu
        rw [ValuationSubring.inv_coe_eq_coe_inv_aux]
        exact hu
      ⟩
    val_inv := by
      simp only [map_inv₀, inv_pow, MulMemClass.mk_mul_mk, map_inv, mul_assoc]
      simp only [← mul_assoc (algebraMap M L u1.1.1), isUnit_iff_ne_zero, ne_eq, map_eq_zero, ZeroMemClass.coe_eq_zero, Units.ne_zero, not_false_eq_true, IsUnit.mul_inv_cancel, one_mul]
      simp only [isUnit_iff_ne_zero, ne_eq, pow_eq_zero_iff', ZeroMemClass.coe_eq_zero,
        Units.ne_zero, false_and, not_false_eq_true, IsUnit.mul_inv_cancel]
      rfl
    inv_val := by
      simp only [map_inv₀, inv_pow, MulMemClass.mk_mul_mk, mul_assoc]
      simp only [← mul_assoc (u.1.1 ^ n1)⁻¹, isUnit_iff_ne_zero, ne_eq, map_eq_zero, ZeroMemClass.coe_eq_zero, Units.ne_zero, not_false_eq_true, IsUnit.mul_inv_cancel, one_mul]
      simp only [isUnit_iff_ne_zero, ne_eq, pow_eq_zero_iff', ZeroMemClass.coe_eq_zero,
        Units.ne_zero, false_and, not_false_eq_true, IsUnit.inv_mul_cancel, one_mul, map_eq_zero]
      rfl
  }
  apply IsDiscreteValuationRing.unit_mul_pow_congr_pow (p := πL) (q := πL) hirrL hirrL u2 u3 _ _
  simp only [← MulMemClass.coe_mul, ← SubmonoidClass.coe_pow] at hnu1
  apply Subtype.coe_inj.1 hnu1

open Polynomial Algebra

theorem AlgEquiv.restrictNormalHom_restrictScalarsHom {x : (L ≃ₐ[M] L)} : AlgEquiv.restrictNormalHom M (AlgEquiv.restrictScalarsHom K x) = 1 := by sorry

def i (s : L ≃ₐ[K] L) (hs : (restrictNormalHom M) s = σ) (a : { x // x ∈ ((restrictNormalHom (K₁ := L) M) ⁻¹' {σ}).toFinset }) (ha : a ∈ (⇑(restrictNormalHom M) ⁻¹' {σ}).toFinset.attach) : L ≃ₐ[M] L where
  toFun x := (s⁻¹ * a) x
  invFun x := (a.1⁻¹ * s) x
  left_inv := by
    simp only [mul_apply, Function.LeftInverse]
    intro x
    rw [← eq_symm_apply, ← eq_symm_apply]
    rfl
  right_inv := by
    simp only [mul_apply, Function.RightInverse, Function.LeftInverse]
    intro x
    rw [← eq_symm_apply, ← eq_symm_apply]
    rfl
  map_mul' x y := by
    simp only [mul_apply, _root_.map_mul]
  map_add' x y := by simp only [mul_apply, _root_.map_add]
  commutes' x := by
    rcases a with ⟨a, ha'⟩
    simp only [Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at ha'
    simp only [mul_apply]
    rw [← AlgEquiv.restrictNormal_commutes,  ← AlgEquiv.restrictNormal_commutes]
    have hs : s.restrictNormal M = σ := hs
    have ha' : a.restrictNormal M = σ := ha'
    have hinv : (s⁻¹.restrictNormal M) = (s.restrictNormal M)⁻¹ := by
      apply (restrictNormalHom M).map_inv
    rw [hinv, hs, ha']
    have hx : σ⁻¹ (σ x) = x := by
      rw [← eq_symm_apply]
      rfl
    rw [hx]


theorem aux_10 (σ : M ≃ₐ[K] M) (s : L ≃ₐ[K] L) (hs : (restrictNormalHom M) s = σ) (x : PowerBasis 𝒪[K] 𝒪[L]) : ∏ x_1 ∈ (⇑(restrictNormalHom M) ⁻¹' {σ}).toFinset.attach, (x_1.1 x.gen.1 - x.gen.1) = ∏ x_1 ∈ (⊤ : Set (L ≃ₐ[M] L)).toFinset, (s (x_1 ↑x.gen) - ↑x.gen) := by
  apply Finset.prod_bij (i σ s hs)
  · intro a ha
    simp only [i, Set.top_eq_univ, Set.toFinset_univ, mul_apply, Finset.mem_univ]
  · intro a1 ha1 a2 ha2 ha
    simp only [i, mul_apply, AlgEquiv.mk.injEq, Equiv.mk.injEq] at ha
    rcases ha with ⟨ha1, ha2⟩
    ext x
    apply AlgEquiv.injective s⁻¹
    apply congr_fun ha1
  · intro b hb
    let a' : { x // x ∈ ((restrictNormalHom M (K₁ := L)) ⁻¹' {σ}).toFinset} := {
      val := s * ((restrictScalarsHom K) b)
      property := by
        simp only [Set.mem_toFinset, Set.mem_preimage, _root_.map_mul, Set.mem_singleton_iff, hs, AlgEquiv.restrictNormalHom_restrictScalarsHom, mul_one]
    }
    have ha : a' ∈ (⇑(restrictNormalHom M) ⁻¹' {σ}).toFinset.attach := Finset.mem_attach (⇑(restrictNormalHom M) ⁻¹' {σ}).toFinset a'
    use a'
    use ha
    simp only [i, a']
    simp_rw [inv_mul_cancel_left, mul_inv_rev, inv_mul_cancel_right]
    rfl
  · intro a ha
    simp only [i, mul_apply, AlgEquiv.coe_mk, Equiv.coe_fn_mk, sub_left_inj]
    rw [← eq_symm_apply, eq_symm_apply, ← symm_symm s, eq_symm_apply]
    rfl

theorem algEquiv_PowerBasis_mem_valuationSubring (x : PowerBasis 𝒪[K] 𝒪[L]) : ∀ t : (L ≃ₐ[M] L), t x.gen ∈ 𝒪[L] := by
  intro t
  rw [mem_integer_iff, val_map_le_one_iff, ← mem_integer_iff]
  exact SetLike.coe_mem x.gen
  exact algEquiv_preserve_val_of_complete t


theorem algEquiv_PowerBasis_mem_aroots_aux (x : PowerBasis 𝒪[K] 𝒪[L]) : ∀ t : (L ≃ₐ[M] L), ⟨t x.gen, algEquiv_PowerBasis_mem_valuationSubring x t⟩ ∈ (minpoly (↥𝒪[M]) x.gen).aroots 𝒪[L] := by
  intro t
  simp only [mem_roots', ne_eq, IsRoot.def, eval_map_algebraMap]
  constructor
  · by_contra hc
    apply minpoly.ne_zero (A := 𝒪[M]) (IsIntegral.isIntegral x.gen)
    apply_fun Polynomial.map (algebraMap ↥𝒪[M] ↥𝒪[L])
    simp only [Polynomial.map_zero]
    exact hc
    exact Polynomial.map_injective (algebraMap 𝒪[M] 𝒪[L]) (IsValExtension.integerAlgebra_injective M L)
  · have hmem := mem_decompositionGroup t
    simp only [← DecompositionGroup.restrictValuationSubring_apply' hmem, SetLike.eta, aeval_algHom_apply, minpoly.aeval (↥𝒪[M]) x.gen]
    exact map_zero (DecompositionGroup.restrictValuationSubring' hmem)

theorem algEquiv_valuationSubring {s : L ≃ₐ[K] L} (t : 𝒪[L]) : s t ∈ 𝒪[L] := by
  rw [← DecompositionGroup.restrictValuationSubring_apply']
  refine SetLike.coe_mem ((DecompositionGroup.restrictValuationSubring' ?h) t)
  exact mem_decompositionGroup s

theorem algEquiv_eq_refl_of_map_powerbasis {s : L ≃ₐ[K] L} {σ : M ≃ₐ[K] M} (hs : s.restrictNormal M = σ) (y : PowerBasis 𝒪[K] 𝒪[M]) (hc : s ((algebraMap M L) ↑y.gen) - (algebraMap M L) ↑y.gen = 0) : σ = AlgEquiv.refl := by
  simp only [sub_eq_zero, ← AlgEquiv.restrictNormal_commutes, hs] at hc
  apply FaithfulSMul.algebraMap_injective M L at hc
  rw [eq_iff_ValuationSubring]
  apply PowerBasis.algHom_ext' y
  rw [← Subtype.val_inj, AlgEquiv.restrictValuationSubring_apply, AlgEquiv.restrictValuationSubring_apply, coe_refl, id_eq]
  exact hc


instance : IsScalarTower 𝒪[K] 𝒪[M] 𝒪[L] where
  smul_assoc x y z := SetLike.coe_eq_coe.mp (IsScalarTower.smul_assoc x.1 y.1 z.1)

instance : NoZeroSMulDivisors 𝒪[M] 𝒪[L] :=  NoZeroSMulDivisors.iff_algebraMap_injective.mpr (IsValExtension.integerAlgebra_injective M L)


def i1 (x : PowerBasis 𝒪[K] 𝒪[L]) (a : L ≃ₐ[M] L) (ha : a ∈ Finset.univ) : { y // y ∈ (Polynomial.map (algebraMap ↥𝒪[M] ↥𝒪[L]) (minpoly (↥𝒪[M]) x.gen)).roots } := ⟨⟨a x.gen, algEquiv_PowerBasis_mem_valuationSubring x a⟩, algEquiv_PowerBasis_mem_aroots_aux x a⟩

def i2 (x : PowerBasis 𝒪[K] 𝒪[L]) (a : 𝒪[L]) (ha : a ∈ (Polynomial.map (algebraMap ↥𝒪[M] ↥𝒪[L]) (minpoly (↥𝒪[M]) x.gen)).roots) :  { y // y ∈ (Polynomial.map (algebraMap ↥𝒪[M] ↥𝒪[L]) (minpoly (↥𝒪[M]) x.gen)).roots } := ⟨a, ha⟩

variable [Algebra.IsSeparable 𝒪[M] 𝒪[L]] [Normal M L]

set_option maxHeartbeats 0

open IntermediateField

theorem AlgEquiv.mem_of_all_apply_eq_self (l : L) (hx : ∀ σ : L ≃ₐ[M] L, σ l = l) : ∃ m : M, algebraMap M L m = l := by
  have hfix : fixedField (⊤ : Subgroup (L ≃ₐ[M] L)) = (⊥ : IntermediateField M L) := by
    have : fixedField (⊤ : Subgroup (L ≃ₐ[M] L)) = fixedField (fixingSubgroup (⊥ : IntermediateField M L)) := by
      simp [IntermediateField.fixingSubgroup_bot]
    rw [this]
    haveI : IsGalois M L := IsGalois.mk
    apply IsGalois.fixedField_fixingSubgroup
  have hmem : l ∈ fixedField (⊤ : Subgroup (L ≃ₐ[M] L)) :=  fun m ↦ hx ((⊤ : Subgroup (L ≃ₐ[M] L)).subtype m)
  rw [hfix] at hmem
  exact hmem

def i4 (x : PowerBasis 𝒪[K] 𝒪[L]) (a : L ≃ₐ[M] L) (ha : a ∈ (⊤ : Set (L ≃ₐ[M] L)).toFinset) : L := a x.gen


def i5 (x : PowerBasis 𝒪[K] 𝒪[L]) (n : ℕ) (σ : L ≃ₐ[M] L) (a : Multiset L) (ha : a ∈ Multiset.powersetCard ((∏ x ∈ @Finset.image (L ≃ₐ[M] L) L _ (fun t ↦ t x.gen) (@Finset.univ (L ≃ₐ[M] L) (fintype M L)), (X - C x)).natDegree - n) (Multiset.map (fun t ↦ t ↑x.gen) (@Finset.univ (L ≃ₐ[M] L) (fintype M L)).val).dedup) : Multiset L :=
  Multiset.map (fun t => σ.symm t) a

theorem PowerBasis.algHom_ext_aux {a1 a2 : L ≃ₐ[M] L} (x : PowerBasis 𝒪[K] 𝒪[L]) (ha : (⟨⟨a1 x.gen.1, algEquiv_PowerBasis_mem_valuationSubring x a1⟩, algEquiv_PowerBasis_mem_aroots_aux x a1⟩ : { y // y ∈ (Polynomial.map (algebraMap ↥𝒪[M] ↥𝒪[L]) (minpoly (↥𝒪[M]) x.gen)).roots }) = (⟨⟨a2 x.gen.1, algEquiv_PowerBasis_mem_valuationSubring x a2⟩, algEquiv_PowerBasis_mem_aroots_aux x a2⟩ : { y // y ∈ (Polynomial.map (algebraMap ↥𝒪[M] ↥𝒪[L]) (minpoly (↥𝒪[M]) x.gen)).roots })) : a1 = a2 := by
  rw [eq_iff_ValuationSubring]
  apply_fun restrictScalars 𝒪[K]
  apply PowerBasis.algHom_ext' x
  simp only [Subtype.mk.injEq, ← AlgEquiv.restrictValuationSubring_apply, Subtype.val_inj] at ha
  simp only [restrictScalars_apply]
  exact ha
  exact restrictScalarsHom_injective ↥𝒪[K]

theorem aux_15 (x : PowerBasis 𝒪[K] 𝒪[L]) : ∏ t ∈ (⊤ : Set (L ≃ₐ[M] L)).toFinset, (X - C (t x.gen)) = ∏ t ∈ ((fun a ↦ a ↑x.gen) '' (@Set.univ (L ≃ₐ[M] L))).toFinset, (X - C t) := by
  apply Finset.prod_bij (i4 x)
  · intro a ha
    simp only [Set.image_univ, Set.toFinset_range, i4, Finset.mem_image, Finset.mem_univ, true_and, exists_apply_eq_apply]
  · intro a1 ha1 a2 ha2 ha
    simp only [i4] at ha
    rw [eq_iff_ValuationSubring]
    apply_fun restrictScalars 𝒪[K]
    apply PowerBasis.algHom_ext' x
    rw [← AlgEquiv.restrictValuationSubring_apply, ← AlgEquiv.restrictValuationSubring_apply] at ha
    simp only [Subtype.val_inj] at ha
    simp only [restrictScalars_apply]
    exact ha
    exact AlgEquiv.restrictScalars_injective ↥𝒪[K]
  · simp only [i4]
    intro b hb
    simp only [Set.mem_toFinset, Set.mem_image] at hb
    obtain ⟨a, ha⟩ := hb
    use a
    simp only [Set.top_eq_univ, Set.toFinset_univ, Finset.mem_univ, exists_const]
    exact ha.2
  · intro a ha
    simp only [i4]

theorem aux_18 {n : ℕ} (σ : L ≃ₐ[M] L) (x : PowerBasis 𝒪[K] 𝒪[L]) {a : Multiset L} (ha1 : a ≤ (Multiset.map (fun t ↦ t ↑x.gen) (@Finset.univ (L ≃ₐ[M] L) (fintype M L)).val).dedup) (ha2 : Multiset.card a = (∏ x ∈ (@Finset.image (L ≃ₐ[M] L) L) (fun t ↦ t ↑x.gen) (@Finset.univ (L ≃ₐ[M] L) (fintype M L)), (X - C x)).natDegree - n) : Multiset.map (fun t ↦ σ t) a ≤ Multiset.map (fun t ↦ t ↑x.gen) ((@Finset.univ (L ≃ₐ[M] L) (fintype M L))).val := by
  refine (Multiset.le_iff_subset ?_).mpr ?_
  apply (Multiset.nodup_map_iff_of_inj_on _).2
  · apply Multiset.nodup_of_le ha1
    apply Multiset.nodup_dedup
  · intro a1 ha1 a2 ha2 ha
    apply_fun σ
    exact ha
  · rw [Multiset.subset_iff]
    intro t ht
    rw [Multiset.mem_map] at ht ⊢
    obtain ⟨k, ⟨hk1, hk2⟩⟩ := ht
    apply Multiset.mem_of_subset (Multiset.subset_of_le ha1) at hk1
    rw [Multiset.mem_dedup, Multiset.mem_map] at hk1
    obtain ⟨l, hl⟩ := hk1
    use σ * l
    constructor
    · exact Finset.mem_univ_val (σ * l)
    · rw [mul_apply, hl.2, hk2]

theorem aux_17 {n : ℕ} (x : PowerBasis 𝒪[K] 𝒪[L]) (σ : L ≃ₐ[M] L) : Multiset.map (fun x ↦ (Multiset.map (⇑σ) x).prod) (Multiset.powersetCard ((∏ x ∈ @Finset.image (L ≃ₐ[M] L) L _ (fun t ↦ t x.gen) (@Finset.univ (L ≃ₐ[M] L) (fintype M L)), (X - C x)).natDegree - n) (Multiset.map (fun t ↦ t ↑x.gen) (@Finset.univ (L ≃ₐ[M] L) (fintype M L)).val).dedup) = Multiset.map (fun x ↦ x.prod) (Multiset.powersetCard ((∏ x ∈ @Finset.image (L ≃ₐ[M] L) L _ (fun t ↦ t x.gen) (@Finset.univ (L ≃ₐ[M] L) (fintype M L)), (X - C x)).natDegree - n) (Multiset.map (fun t ↦ t ↑x.gen) (@Finset.univ (L ≃ₐ[M] L) (fintype M L)).val).dedup) := by
  symm
  apply Multiset.map_eq_map_of_bij_of_nodup _ _ _ _ (i5 x n σ)
  · intro a ha
    simp only [i5]
    simp only [Multiset.mem_powersetCard, Multiset.card_map] at ha ⊢
    rcases ha with ⟨ha1, ha2⟩
    constructor
    · apply Multiset.le_dedup.2
      constructor
      · apply aux_18 σ.symm x ha1 ha2
      · rw [Multiset.le_dedup] at ha1
        rw [Multiset.nodup_map_iff_of_inj_on]
        apply ha1.2
        intro x hx y hy hxy
        apply_fun σ.symm
        apply hxy
    · exact ha2
  · intro a1 ha1 a2 ha2 ha
    simp only [i5] at ha
    apply_fun Multiset.map (fun t ↦ σ.symm t)
    apply ha
    apply Multiset.map_injective
    exact AlgEquiv.injective σ.symm
  · intro b hb
    simp only [i5]
    use Multiset.map (fun t => σ t) b
    simp only [Multiset.map_map, Function.comp_apply, symm_apply_apply, Multiset.map_id', Multiset.mem_powersetCard, Multiset.card_map, exists_prop, and_true]
    simp only [Multiset.mem_powersetCard] at hb
    rcases hb with ⟨hb1, hb2⟩
    constructor
    · apply Multiset.le_dedup.2
      constructor
      · apply aux_18 σ x hb1 hb2
      · rw [Multiset.nodup_map_iff_of_inj_on]
        rw [Multiset.le_dedup] at hb1
        apply hb1.2
        intro x hx y hy hxy
        apply_fun σ
        apply hxy
    · exact hb2
  · intro a ha
    simp only [i5]
    simp only [Multiset.map_map, Function.comp_apply, apply_symm_apply, Multiset.map_id']
  · apply Multiset.Nodup.powersetCard
    apply Multiset.nodup_dedup
  · apply Multiset.Nodup.powersetCard
    apply Multiset.nodup_dedup


theorem aux_16 (x : PowerBasis 𝒪[K] 𝒪[L]) : ∀ n : ℕ, ∃ m : M, algebraMap M L m = (∏ t ∈ (⊤ : Set (L ≃ₐ[M] L)).toFinset, (X - C (t x.gen))).coeff n := by
  let f := ∏ t ∈ (⊤ : Set (L ≃ₐ[M] L)).toFinset, (X - C (t x.gen))
  intro n
  apply AlgEquiv.mem_of_all_apply_eq_self
  intro σ
  by_cases hc : n ≤ f.natDegree
  · rw [Polynomial.coeff_eq_esymm_roots_of_card _ hc]
    simp only [_root_.map_mul, _root_.map_pow, _root_.map_neg, _root_.map_one]
    have hlead : f.leadingCoeff = 1 := by
      simp only [f]
      apply Monic.leadingCoeff
      apply monic_prod_of_monic
      intro i hi
      exact monic_X_sub_C (i ↑x.gen)
    rw [hlead]
    simp only [_root_.map_one, one_mul, mul_eq_mul_left_iff, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, ne_eq, false_and, or_false, f]
    simp only [aux_15, Polynomial.roots_prod_X_sub_C, Set.image_univ, Set.toFinset_range, Finset.image_val, Multiset.esymm, map_multiset_sum, Multiset.map_map, Function.comp_apply, map_multiset_prod]
    congr 1
    apply aux_17 x σ
    · symm
      rw [← map_id (R := L) (p := f)]
      apply natDegree_eq_card_roots' (i := RingHom.id L)
      refine splits_prod (RingHom.id L) ?_
      intro i hi
      exact splits_X_sub_C (RingHom.id L)
  · push_neg at hc
    simp only [coeff_eq_zero_of_natDegree_lt hc, f]
    exact map_zero σ

theorem Polynomial.exsits_of_coeff_aux {f : L[X]} (hcoeff : ∀ n : ℕ, ∃ m : M, algebraMap M L m = f.coeff n) : ∃ f' : M[X], Polynomial.map (algebraMap M L) f' = f := by
  let i : (n : ℕ) → {x // algebraMap M L x = f.coeff n} := by
      intro n
      let m := Classical.choose (hcoeff n)
      let hm := Classical.choose_spec (hcoeff n)
      exact ⟨m, hm⟩
  use ∑ n ∈ f.support, C (i n).1 * X ^ n
  simp only [i, Polynomial.map_sum, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X]
  conv =>
    enter [1, 2]
    intro x
    rw [Classical.choose_spec (hcoeff x)]
  exact Eq.symm (as_sum_support_C_mul_X_pow f)

theorem PowerBasis.algHom_ext_aux' (x : PowerBasis 𝒪[K] 𝒪[L]) {a1 a2 : L ≃ₐ[M] L} (ha : a1 x.gen = a2 x.gen) : a1 = a2 := by
  rw [eq_iff_ValuationSubring]
  apply_fun restrictScalars 𝒪[K]
  apply PowerBasis.algHom_ext' x
  rw [← AlgEquiv.restrictValuationSubring_apply, ← AlgEquiv.restrictValuationSubring_apply] at ha
  simp only [Subtype.val_inj] at ha
  simp only [restrictScalars_apply]
  exact ha
  exact restrictScalarsHom_injective ↥𝒪[K]

theorem algebraMap_comp_aux : (algebraMap (↥𝒪[M]) L) = (algebraMap 𝒪[L] L).comp (algebraMap (↥𝒪[M]) 𝒪[L]) := rfl

theorem algebraMap_comp_Injective_aux : Function.Injective (algebraMap 𝒪[M] L) := by
  rw [algebraMap_comp_aux, RingHom.coe_comp]
  apply Function.Injective.comp
  exact IsFractionRing.injective (↥𝒪[L]) L
  exact IsValExtension.integerAlgebra_injective M L

theorem mem_aroots_of_mem_aroots_valuationSubring {t : 𝒪[L]} (x : PowerBasis 𝒪[K] 𝒪[L]) (ht : t ∈ (Polynomial.map (algebraMap 𝒪[M] 𝒪[L]) (minpoly (↥𝒪[M]) x.gen)).roots) : t.1 ∈ (Polynomial.map (algebraMap 𝒪[M] L) (minpoly (↥𝒪[M]) x.gen)).roots := by
  rw [algebraMap_comp_aux, ← Polynomial.map_map]
  apply Multiset.mem_of_le
  · apply Polynomial.map_roots_le
    simp only [Polynomial.map_map]
    apply (Polynomial.map_ne_zero_iff _).2 (minpoly.ne_zero (IsIntegral.isIntegral x.gen))
    exact algebraMap_comp_Injective_aux
  · simp only [Multiset.mem_map]
    use t
    use ht
    rfl

theorem algEquiv_mem_minpoly_roots (x : PowerBasis 𝒪[K] 𝒪[L]) : Multiset.map (fun a ↦ a ↑x.gen) (@Finset.univ (L ≃ₐ[M] L) (fintype M L)).val ≤ (Polynomial.map (algebraMap (↥𝒪[M]) L) (minpoly (↥𝒪[M]) x.gen)).roots := by
  refine (Multiset.le_iff_subset ?_).mpr ?_
  · apply (Multiset.nodup_map_iff_of_inj_on _).2
    · exact Finset.univ.nodup
    · intro a1 ha1 a2 ha2 ha
      apply PowerBasis.algHom_ext_aux' x ha
  · refine Multiset.subset_iff.mpr ?_
    intro t ht
    rw [Multiset.mem_map] at ht
    obtain ⟨a, ha⟩ := ht
    rw [Finset.mem_val] at ha
    rcases ha with ⟨ha1, ha2⟩
    rw [← ha2]
    rw [algebraMap_comp_aux, ← Polynomial.map_map]
    apply Multiset.mem_of_le
    · apply Polynomial.map_roots_le
      simp only [Polynomial.map_map]
      apply (Polynomial.map_ne_zero_iff _).2 (minpoly.ne_zero (IsIntegral.isIntegral x.gen))
      exact algebraMap_comp_Injective_aux
    · have h := algEquiv_PowerBasis_mem_aroots_aux x a
      simp only [aroots_def, Multiset.mem_map] at h
      refine Multiset.mem_map.mpr ?_
      use (⟨a x.gen, algEquiv_PowerBasis_mem_valuationSubring x a⟩ : 𝒪[L])
      exact ⟨h, rfl⟩

instance : FaithfulSMul 𝒪[M] M where
  eq_of_smul_eq_smul := by
    intro m1 m2 ha
    have ha' : ∀ a : M, (m1 : M) • a = (m2 : M) • a := fun a ↦ ha a
    simp only [smul_eq_mul, mul_eq_mul_right_iff, SetLike.coe_eq_coe] at ha'
    replace ha := ha' 1
    simp only [one_ne_zero, or_false] at ha
    exact ha

theorem aux_14 (x : PowerBasis 𝒪[K] 𝒪[L]) : ∏ x_1 : L ≃ₐ[M] L, (X - C (⟨x_1 ↑x.gen, algEquiv_PowerBasis_mem_valuationSubring x x_1⟩ : 𝒪[L])) = ∏ t : { y // y ∈ (Polynomial.map (algebraMap 𝒪[M] 𝒪[L]) (minpoly 𝒪[M] x.gen)).roots}, (X - C t.1) := by
  apply Finset.prod_bij (i1 x)
  · intro a ha
    simp only [i1, Finset.mem_univ]
  · intro a1 ha1 a2 ha2 ha
    simp only [i1] at ha
    apply PowerBasis.algHom_ext_aux x ha
  · intro b hb
    simp only [i1]
    simp only [Finset.mem_univ, exists_const]
    let f := ∏ t ∈ (⊤ : Set (L ≃ₐ[M] L)).toFinset, (X - C (t x.gen))
    have hcoeff : ∀ n : ℕ, ∃ m : M, algebraMap M L m = f.coeff n := by
      simp only [f]
      apply aux_16
    obtain ⟨f', hf'⟩ := Polynomial.exsits_of_coeff_aux hcoeff
    have hdegree : f'.degree = f.degree := by
      rw [← hf']
      symm
      apply Polynomial.degree_map_eq_of_injective (FaithfulSMul.algebraMap_injective M L)
    have hdegree' : f.degree = Nat.card (L ≃ₐ[M] L) := by
      simp only [f, degree_prod, Set.top_eq_univ, Set.toFinset_univ, degree_X_sub_C, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]
    by_contra hc
    push_neg at hc
    have hlt : f'.degree < (minpoly 𝒪[M] x.gen).degree := by
      rw [hdegree, hdegree']
      let i : (L ≃ₐ[M] L) → L := fun a ↦ a ↑x.gen
      let s := Multiset.map (fun a => a x.gen) (@Finset.univ (L ≃ₐ[M] L) (fintype M L)).val
      have hs : Multiset.card s = Nat.card (L ≃ₐ[M] L) := by
        simp only [s, Multiset.card_map, Finset.card_val, Finset.card_univ, Nat.card_eq_fintype_card]
      have hr : s < (Polynomial.map (algebraMap 𝒪[M] L) (minpoly 𝒪[M] x.gen)).roots := by
        apply lt_of_le_of_ne (algEquiv_mem_minpoly_roots x)
        have h1 : ¬ (Polynomial.map (algebraMap (↥𝒪[M]) L) (minpoly (↥𝒪[M]) x.gen)).roots ⊆ s := by
          rw [Multiset.subset_iff]
          push_neg
          use b.1.1
          constructor
          · apply mem_aroots_of_mem_aroots_valuationSubring x b.2
          · by_contra hc'
            simp only [s, Multiset.mem_map] at hc'
            absurd hc
            push_neg
            obtain ⟨k, hk⟩ := hc'
            use k
            simp only [hk, Subtype.coe_eta]
        symm
        by_contra hc
        exact h1 (subset_of_subset_of_eq (fun ⦃a⦄ a ↦ a) hc)
      apply Multiset.card_lt_card at hr
      rw [← hs, Polynomial.coe_lt_degree]
      apply lt_of_lt_of_le hr
      have hdegree : (minpoly (↥𝒪[M]) x.gen).natDegree = (Polynomial.map (algebraMap 𝒪[M] L) (minpoly (↥𝒪[M]) x.gen)).natDegree := by
        symm
        apply Polynomial.natDegree_map_eq_of_injective (algebraMap_comp_Injective_aux)
      rw [hdegree]
      exact card_roots' (Polynomial.map (algebraMap (↥𝒪[M]) L) (minpoly (↥𝒪[M]) x.gen))
    absurd hlt
    push_neg
    have hmp : (minpoly M (algebraMap 𝒪[L] L x.gen)) = Polynomial.map (algebraMap 𝒪[M] M) (minpoly 𝒪[M] x.gen) := minpoly.isIntegrallyClosed_eq_field_fractions _ _ (IsIntegral.isIntegral x.gen)
    have hdegree' : (minpoly 𝒪[M] x.gen).degree = (Polynomial.map (algebraMap (↥𝒪[M]) M) (minpoly (↥𝒪[M]) x.gen)).degree := by
      symm
      apply Polynomial.degree_map_eq_of_injective
      refine FaithfulSMul.algebraMap_injective 𝒪[M] M
    rw [hdegree', ← hmp]
    apply minpoly.min M _
    · simp only [Function.Injective.monic_map_iff (FaithfulSMul.algebraMap_injective M L), hf', f]
      apply monic_prod_of_monic
      intro i hi
      exact monic_X_sub_C (i ↑x.gen)
    · simp only [aeval_def, eval₂_eq_eval_map, hf', f, eval_prod, eval_sub, eval_C, eval_X, Set.top_eq_univ, Set.toFinset_univ]
      apply Finset.prod_eq_zero_iff.2
      use .refl
      refine ⟨Finset.mem_univ AlgEquiv.refl, sub_eq_zero_of_eq rfl⟩
  · intro a ha
    simp only [i1]


theorem aux_19 (x : PowerBasis 𝒪[K] 𝒪[L]) : (Multiset.map (fun a ↦ X - C a) (Polynomial.map (algebraMap ↥𝒪[M] ↥𝒪[L]) (minpoly (↥𝒪[M]) x.gen)).roots) =  (Multiset.map (fun a ↦ X - C a.1) (@Finset.univ { y // y ∈ (Polynomial.map (algebraMap ↥𝒪[M] ↥𝒪[L]) (minpoly (↥𝒪[M]) x.gen)).roots }).val) := by
  apply Multiset.map_eq_map_of_bij_of_nodup _ _ ?_ ?_ (i2 x)
  · intro a ha
    simp only [i2, Finset.mem_val, Finset.mem_univ]
  · intro a1 ha1 a2 ha2 ha
    simp only [i2, Subtype.mk.injEq] at ha
    exact ha
  · intro b hb
    use b.1
    use b.2
    simp only [i2]
  · intro a ha
    simp only [i2]
  · apply nodup_roots
    apply Polynomial.Separable.map
    apply Algebra.IsSeparable.isSeparable
  · exact Finset.univ.nodup


theorem mem_aroots_valuationSubring_of_mem_aroots {t : L} (x : PowerBasis 𝒪[K] 𝒪[L]) (ht : t ∈ (Polynomial.map (algebraMap 𝒪[M] L) (minpoly (↥𝒪[M]) x.gen)).roots) : t ∈ Multiset.map Subtype.val (map (algebraMap ↥𝒪[M] ↥𝒪[L]) (minpoly (↥𝒪[M]) x.gen)).roots := by
  simp only [Multiset.mem_map, mem_roots', IsRoot.def, eval_map_algebraMap, Subtype.exists, exists_and_right, exists_and_left, exists_eq_right]
  simp only [mem_roots', IsRoot.def, eval_map_algebraMap] at ht
  rcases ht with ⟨hc1, hc2⟩
  constructor
  · rw [Polynomial.map_ne_zero_iff] at hc1 ⊢
    · exact hc1
    · exact IsValExtension.integerAlgebra_injective M L
    · exact algebraMap_comp_Injective_aux
  · have hint : IsIntegral 𝒪[M] t := by
      simp only [IsIntegral, RingHom.IsIntegralElem]
      use (minpoly (↥𝒪[M]) x.gen)
      constructor
      · refine minpoly.monic ?h.left.hx
        exact IsIntegral.isIntegral x.gen
      · simp only [aeval_def] at hc2
        exact hc2
    obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝒪[L])).1 hint
    rw [← hy]
    have h : (algebraMap (↥𝒪[L]) L) y ∈ 𝒪[L] := by
      have : (algebraMap 𝒪[L] L) y = (y : L) := rfl
      rw [this]
      simp only [SetLike.coe_mem]
    use h
    rw [← hy] at hc2
    rw [← Subtype.val_inj, ZeroMemClass.coe_zero]
    rw [← hc2]
    simp only [aeval_def, eval₂, Polynomial.sum_def, SubmonoidClass.mk_pow, AddSubmonoidClass.coe_finset_sum, Subring.coe_mul]
    rfl

theorem Polynomial.roots_of_valuationSubring (x : PowerBasis 𝒪[K] 𝒪[L]) :  Multiset.card (Polynomial.map (algebraMap ↥𝒪[M] ↥𝒪[L]) (minpoly (↥𝒪[M]) x.gen)).roots = Multiset.card (Polynomial.map (algebraMap 𝒪[M] L) (minpoly (↥𝒪[M]) x.gen)).roots := by
  apply Multiset.card_eq_card_of_rel (r := fun a b => a.1 = b)
  rw [← Multiset.rel_map_left, Multiset.rel_eq]
  ext t
  rw [Multiset.count_eq_of_nodup, Multiset.count_eq_of_nodup]
  by_cases hc : t ∈ Multiset.map Subtype.val (Polynomial.map (algebraMap ↥𝒪[M] ↥𝒪[L]) (minpoly (↥𝒪[M]) x.gen)).roots
  · have hc' : t ∈ (Polynomial.map (algebraMap (↥𝒪[M]) L) (minpoly (↥𝒪[M]) x.gen)).roots := by
      obtain ⟨k, hk⟩ := Multiset.mem_map.1 hc
      rw [← hk.2]
      apply mem_aroots_of_mem_aroots_valuationSubring _ hk.1
    simp only [hc, ↓reduceIte, hc']
  · have hc' : ¬ t ∈ (Polynomial.map (algebraMap (↥𝒪[M]) L) (minpoly (↥𝒪[M]) x.gen)).roots := by
      by_contra hcon
      absurd hc
      apply mem_aroots_valuationSubring_of_mem_aroots _ hcon
    simp only [hc, ↓reduceIte, hc']
  · apply nodup_roots
    apply Polynomial.Separable.map
    apply Algebra.IsSeparable.isSeparable
  · refine (Multiset.nodup_map_iff_of_injective ?_).mpr ?_
    exact Subtype.val_injective
    apply nodup_roots
    apply Polynomial.Separable.map
    apply Algebra.IsSeparable.isSeparable

theorem aux_11 (x : PowerBasis 𝒪[K] 𝒪[L]) : Polynomial.map (algebraMap 𝒪[M] 𝒪[L]) (minpoly 𝒪[M] x.gen) = ∏ t ∈ (⊤ : Set (L ≃ₐ[M] L)).toFinset, (X - C (⟨t x.gen, algEquiv_PowerBasis_mem_valuationSubring x t⟩ : 𝒪[L])) := by
  rw [← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (p := (Polynomial.map (algebraMap 𝒪[M] 𝒪[L]) (minpoly 𝒪[M] x.gen)))]
  simp only [Set.top_eq_univ, Set.toFinset_univ, aux_14 x, Finset.prod_eq_multiset_prod]
  rw [aux_19 x]
  apply Polynomial.Monic.map
  apply minpoly.monic (IsIntegral.isIntegral x.gen)
  have h1 : (minpoly M (algebraMap 𝒪[L] L x.gen)) = Polynomial.map (algebraMap 𝒪[M] M) (minpoly 𝒪[M] x.gen) := minpoly.isIntegrallyClosed_eq_field_fractions _ _ (IsIntegral.isIntegral x.gen)
  have h2 : (algebraMap M L).comp (algebraMap 𝒪[M] M) = algebraMap 𝒪[M] L := rfl
  simp only [Polynomial.roots_of_valuationSubring x, ← h2, ← Polynomial.map_map, ← h1]
  rw [Polynomial.natDegree_map_eq_of_injective, ← Polynomial.natDegree_map_eq_of_injective (f := algebraMap 𝒪[M] M), ← h1, ← Polynomial.natDegree_map_eq_of_injective (f := algebraMap M L)]
  symm
  apply Polynomial.natDegree_eq_card_roots'
  apply Normal.splits
  infer_instance
  exact FaithfulSMul.algebraMap_injective M L
  exact FaithfulSMul.algebraMap_injective (↥𝒪[M]) M
  exact IsValExtension.integerAlgebra_injective M L

theorem aux_1 (σ : M ≃ₐ[K] M) (hσ : σ ≠ .refl) (x : PowerBasis 𝒪[K] 𝒪[L]) (y : PowerBasis 𝒪[K] 𝒪[M]) [Algebra.IsSeparable (IsLocalRing.ResidueField 𝒪[K]) (IsLocalRing.ResidueField 𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField 𝒪[M]) (IsLocalRing.ResidueField 𝒪[L])] : ∃ t : 𝒪[L], (∏ x_1 ∈ (⇑(restrictNormalHom M (K₁ := L)) ⁻¹' {σ}).toFinset.attach, (x_1.1 x.gen - x.gen)) = (algebraMap M L) (σ ↑y.gen - ↑y.gen) * t := by
  let a := (algebraMap M L) (σ ↑y.gen - ↑y.gen)
  let b := (∏ x_1 ∈ (⇑(restrictNormalHom M (K₁ := L)) ⁻¹' {σ}).toFinset.attach, (x_1.1 x.gen - x.gen))
  have hin : ∀ t : (L ≃ₐ[M] L), t x.gen ∈ 𝒪[L] := fun t ↦ algEquiv_PowerBasis_mem_valuationSubring x t
  let f := ∏ t ∈ (⊤ : Set (L ≃ₐ[M] L)).toFinset, (C (⟨t x.gen, hin t⟩ : 𝒪[L]) - X)
  obtain ⟨s, hs⟩ := AlgEquiv.restrictNormalHom_surjective L σ
  have hin' : ∀ t : 𝒪[L], s t ∈ 𝒪[L] := algEquiv_valuationSubring
  let e : 𝒪[L] →+* 𝒪[L] := {
      toFun := fun t => ⟨s t, hin' t⟩
      map_one' := by
        simp only [OneMemClass.coe_one, _root_.map_one]
        rfl
      map_mul' := by
        simp only [Subring.coe_mul, _root_.map_mul, MulMemClass.mk_mul_mk, implies_true]
      map_zero' := by
        simp only [ZeroMemClass.coe_zero, _root_.map_zero]
        rfl
      map_add' := by
        simp only [Subring.coe_add, _root_.map_add, AddMemClass.mk_add_mk, implies_true]
    }
  let sf := Polynomial.map e f
  let sf' := ∏ t ∈ (⊤ : Set (L ≃ₐ[K] L)).toFinset, (X - C ((s * t) x.gen))
  have hcoeff : ∀ i : ℕ, coeff sf i = s (coeff f i).1 := by
    intro i
    rw [Polynomial.coeff_map]
    simp only [f, Polynomial.map_prod, e]
    simp only [Polynomial.map_sub, map_X, map_C, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  have hdvd : ∃ t : 𝒪[L], b = a * t := by
    have ha : a = s (algebraMap M L y.gen) - (algebraMap M L y.gen) := by
      simp only [a]
      simp only [_root_.map_sub, sub_left_inj]
      rw [← hs]
      apply AlgEquiv.restrictNormal_commutes
    have hb : b = eval x.gen (sf - f) := by
      rw [eval_sub]
      have heq : eval x.gen f = 0 := by
        simp only [f, eval_prod, eval_sub, eval_X, eval_C, Finset.prod_eq_zero_iff]
        use .refl
        simp only [Set.top_eq_univ, Set.toFinset_univ, Finset.mem_univ, coe_refl, id_eq, sub_self, and_self]
      rw [heq, sub_zero]
      simp only [b, sf, f]
      rw [Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C, mul_apply, Polynomial.eval_prod, eval_sub, eval_C, eval_X, SubmonoidClass.coe_finset_prod,AddSubgroupClass.coe_sub, e, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
      apply aux_10 σ s hs x
    rw [ha, hb, ← eval_C (a := (s (algebraMap M L y.gen) - (algebraMap M L y.gen))) (x := x.gen.1), ← IsValExtension.coe_algebraMap_valuationSubring]
    have hcoeff' : ∀ n : ℕ, ∃ g : 𝒪[K][X], (minpoly 𝒪[M] x.gen).coeff n = aeval y.gen g := by
      intro n
      apply PowerBasis.exists_eq_aeval'
    let i : ℕ → 𝒪[M] := by
      intro n
      let g := Classical.choose (hcoeff' n)
      exact aeval y.gen g
    have hmin : f = (-1) ^ (⊤ : (Set (L ≃ₐ[M] L))).toFinset.card * Polynomial.map (algebraMap 𝒪[M] 𝒪[L]) (minpoly 𝒪[M] x.gen) := by
      have ugly : ∀ x_1 : L ≃ₐ[M] L, - (X - C (⟨x_1 ↑x.gen, hin x_1⟩ : 𝒪[L])) = -1 * (X - C (⟨x_1 ↑x.gen, hin x_1⟩ : 𝒪[L])) := by
        intro t
        ring
      simp only [f, aux_11, ← neg_sub X, ugly, Finset.prod_mul_distrib, Finset.prod_const]
    have hf : ∀ n : ℕ, f.coeff n = (-1) ^ (⊤ : (Set (L ≃ₐ[M] L))).toFinset.card * algebraMap 𝒪[M] 𝒪[L] (i n) := by
      intro n
      simp only [hmin, i]
      rw [← _root_.map_one Polynomial.C, ← _root_.map_neg Polynomial.C, ← _root_.map_pow, coeff_C_mul, coeff_map, ← (hcoeff' n).choose_spec]
    have hin : s ((algebraMap 𝒪[M] 𝒪[L]) y.gen) ∈ 𝒪[L] := hin' ((algebraMap ↥𝒪[M] ↥𝒪[L]) y.gen)
    have hcoeff''' : ∀ n : ℕ, sf.coeff n = ⟨s (f.coeff n), hin' (f.coeff n)⟩ := by
      simp only [← Subtype.val_inj, hcoeff, implies_true]
    have hcoeff'' : ∀ n : ℕ, ∃ t : 𝒪[L], (sf - f).coeff n = (⟨s (algebraMap 𝒪[M] 𝒪[L] y.gen), hin⟩ - algebraMap 𝒪[M] 𝒪[L] y.gen) * t := by
      intro n
      rw [coeff_sub, hcoeff''' n, hf n]
      simp only [← Subtype.val_inj, Subring.coe_mul, SubmonoidClass.coe_pow, NegMemClass.coe_neg, OneMemClass.coe_one, _root_.map_mul, _root_.map_pow, _root_.map_neg, _root_.map_one, AddSubgroupClass.coe_sub, exists_prop, i]
      simp only [SetLike.coe_eq_coe, IsValExtension.coe_algebraMap_integer]
      rw [← mul_sub, aeval_def, eval₂_def, Polynomial.sum]
      simp only [AddSubmonoidClass.coe_finset_sum, Subring.coe_mul, IsValExtension.coe_algebraMap_integer, SubmonoidClass.coe_pow, map_sum, _root_.map_mul, _root_.map_pow, _root_.map_mul]
      simp only [← Function.comp_apply (f := algebraMap M L) (g := algebraMap K M)]
      have ha : (algebraMap M L) ∘ (algebraMap K M) = algebraMap K L := by
        rw [IsScalarTower.algebraMap_eq (R := K) (S := M) (A := L), RingHom.coe_comp]
      have hs : ∀ k : K, s (algebraMap K L k) = algebraMap K L k := s.commutes'
      simp only [ha, ← Finset.sum_sub_distrib, hs _, ← mul_sub]
      set g := (hcoeff' n).choose
      have hsum : ∀ t : ℕ, ∃ l : 𝒪[L], (algebraMap K L) ↑((hcoeff' n).choose.coeff t) * (s ((algebraMap M L) ↑y.gen) ^ t - (algebraMap M L) ↑y.gen ^ t) = (s ((algebraMap M L) ↑y.gen) - (algebraMap M L) ↑y.gen) * l := by
        intro k
        obtain ⟨l, hl⟩ := sub_dvd_pow_sub_pow (⟨s ((algebraMap 𝒪[M] 𝒪[L]) ↑y.gen), hin⟩) ((algebraMap 𝒪[M] 𝒪[L]) y.gen) k
        rw [← Subtype.val_inj] at hl
        simp only [SubmonoidClass.mk_pow,AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, Subring.coe_mul] at hl
        use (algebraMap 𝒪[K] 𝒪[L]) ((hcoeff' n).choose.coeff k) * l
        simp only [← IsValExtension.coe_algebraMap_integer]
        rw [Subring.coe_mul, mul_comm _ (l : L), ← mul_assoc, ← hl, mul_comm]
      use (-1) ^ (⊤ : (Set (L ≃ₐ[M] L))).toFinset.card * ∑ t ∈ (hcoeff' n).choose.support, (hsum t).choose
      simp only [Subring.coe_mul, SubmonoidClass.coe_pow, NegMemClass.coe_neg, OneMemClass.coe_one, AddSubmonoidClass.coe_finset_sum]
      conv_rhs =>
        rw [← mul_assoc]
        enter [1]
        rw [mul_comm]
      rw [mul_assoc]
      simp only [mul_eq_mul_left_iff, Finset.mul_sum]
      congr
      ext i
      simp only [mul_eq_mul_left_iff]
      left
      rw [← (hsum i).choose_spec]
    let i' : ℕ → 𝒪[L] := by
      intro n
      exact Classical.choose (hcoeff'' n)
    let g : 𝒪[L][X] := ∑ n ∈ f.support, monomial n (i' n)
    use (eval x.gen g)
    have h : (eval x.gen (sf - f)) = eval (x.gen) (C (⟨s ((algebraMap 𝒪[M] 𝒪[L]) y.gen), hin⟩  - ((algebraMap 𝒪[M] 𝒪[L]) y.gen))) * (eval x.gen g) := by
      rw [← eval_mul]
      congr
      simp only [Polynomial.ext_iff, g, i', Finset.mul_sum]
      simp only [finset_sum_coeff]
      intro n
      by_cases hcase : f.coeff n = 0
      · simp only [coeff_C_mul, coeff_monomial,  IsValExtension.coe_algebraMap_integer, coeff_sub, mul_ite, mul_zero, Finset.sum_ite_eq', mem_support_iff, ne_eq, ite_not, hcase, ↓reduceIte, sub_zero, ← Subtype.val_inj, hcoeff n, ZeroMemClass.coe_zero, _root_.map_zero]
      · rw [(hcoeff'' n).choose_spec]
        simp only [coeff_C_mul, coeff_monomial, IsValExtension.coe_algebraMap_integer, coeff_sub, mul_ite, mul_zero, Finset.sum_ite_eq', mem_support_iff, ne_eq, ite_not, hcase, ↓reduceIte]
    rw [← Subtype.val_inj] at h
    simp only [h]
    simp only [IsValExtension.coe_algebraMap_integer, _root_.map_sub, eval_sub, eval_C, Subring.coe_mul, AddSubgroupClass.coe_sub]
  simp only [a, b] at hdvd
  exact hdvd


theorem aux_2 (σ : M ≃ₐ[K] M) (x : PowerBasis 𝒪[K] 𝒪[L]) (y : PowerBasis 𝒪[K] 𝒪[M]) [Algebra.IsSeparable (IsLocalRing.ResidueField 𝒪[K]) (IsLocalRing.ResidueField 𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField 𝒪[M]) (IsLocalRing.ResidueField 𝒪[L])] : ∃ t : 𝒪[L], (algebraMap M L) (σ ↑y.gen - ↑y.gen) = (∏ x_1 ∈ (⇑(restrictNormalHom M (K₁ := L)) ⁻¹' {σ}).toFinset.attach, (x_1.1 x.gen - x.gen)) * t := by
  let a := (algebraMap M L) (σ ↑y.gen - ↑y.gen)
  let b := (∏ x_1 ∈ (⇑(restrictNormalHom M (K₁ := L)) ⁻¹' {σ}).toFinset.attach, (x_1.1 x.gen - x.gen))
  have hin : ∀ t : (L ≃ₐ[M] L), t x.gen ∈ 𝒪[L] := fun t ↦ algEquiv_PowerBasis_mem_valuationSubring x t
  let f := ∏ t ∈ (⊤ : Set (L ≃ₐ[M] L)).toFinset, (C (⟨t x.gen, hin t⟩ : 𝒪[L]) - X)
  obtain ⟨s, hs⟩ := AlgEquiv.restrictNormalHom_surjective L σ
  have hin' : ∀ t : 𝒪[L], s t ∈ 𝒪[L] := fun t ↦ algEquiv_valuationSubring t
  let e : 𝒪[L] →+* 𝒪[L] := {
      toFun := fun t => ⟨s t, hin' t⟩
      map_one' := by
        simp only [OneMemClass.coe_one, _root_.map_one]
        rfl
      map_mul' := by
        simp only [Subring.coe_mul, _root_.map_mul, MulMemClass.mk_mul_mk, implies_true]
      map_zero' := by
        simp only [ZeroMemClass.coe_zero, _root_.map_zero]
        rfl
      map_add' := by
        simp only [Subring.coe_add, _root_.map_add, AddMemClass.mk_add_mk, implies_true]
    }
  let sf := Polynomial.map e f
  have hdvd : ∃ t : 𝒪[L], a = b * t := by
    have hy : ∃ g : 𝒪[K][X], eval x.gen (Polynomial.map (algebraMap 𝒪[K] 𝒪[L]) g) = algebraMap 𝒪[M] 𝒪[L] y.gen := by
      obtain ⟨g, hg⟩ := Algebra.exists_eq_aeval_generator (PowerBasis.adjoin_gen_eq_top x) (algebraMap 𝒪[M] 𝒪[L] y.gen)
      use g
      rw [hg]
      simp only [eval_map_algebraMap]
    obtain ⟨g, hg⟩ := hy
    let g_sub_y := Polynomial.map (algebraMap 𝒪[K] 𝒪[M]) g - C y.gen
    have ha : - a = eval x.gen (Polynomial.map e  (Polynomial.map (algebraMap 𝒪[M] 𝒪[L]) g_sub_y)) := by
      simp only [a, g_sub_y]
      have hg' : (Polynomial.map e (Polynomial.map (algebraMap 𝒪[M] 𝒪[L]) (Polynomial.map (algebraMap 𝒪[K] 𝒪[M]) g))) = (Polynomial.map (algebraMap 𝒪[K] 𝒪[L]) g) := by
        rw [Polynomial.map_map (algebraMap 𝒪[K] 𝒪[M]), ← (IsScalarTower.algebraMap_eq 𝒪[K] 𝒪[M] 𝒪[L])]
        ext n
        simp only [coeff_map, e, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, IsValExtension.coe_algebraMap_valuationSubring, AlgEquiv.commutes]
      simp only [_root_.map_sub, Polynomial.map_sub, map_C, hg', eval_sub, eval_map_algebraMap, eval_C, ← eval_map_algebraMap, hg, neg_sub, AddSubgroupClass.coe_sub, IsValExtension.coe_algebraMap_integer,sub_right_inj, e, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, IsValExtension.coe_algebraMap_integer, ← hs]
      apply AlgEquiv.restrictNormal_commutes
    have hdvd : minpoly 𝒪[M] x.gen ∣ g_sub_y := by
      apply minpoly.isIntegrallyClosed_dvd
      exact IsIntegral.isIntegral x.gen
      simp only [g_sub_y, ← eval_map_algebraMap, Polynomial.map_sub, Polynomial.map_map (algebraMap 𝒪[K] 𝒪[M]) (algebraMap 𝒪[M] 𝒪[L]) g, ← (IsScalarTower.algebraMap_eq 𝒪[K] 𝒪[M] 𝒪[L]), eval_sub, hg, map_C, eval_C, sub_self]
    obtain ⟨h, hh⟩ := hdvd
    have hb : b = eval x.gen sf := by
      simp only [b, sf, f]
      rw [Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C, mul_apply, Polynomial.eval_prod, eval_sub, eval_C, eval_X, SubmonoidClass.coe_finset_prod,AddSubgroupClass.coe_sub, e, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
      apply aux_10 σ s hs x
    have hmin : f = (-1) ^ (⊤ : (Set (L ≃ₐ[M] L))).toFinset.card * Polynomial.map (algebraMap 𝒪[M] 𝒪[L]) (minpoly 𝒪[M] x.gen) := by
      have ugly : ∀ x_1 : L ≃ₐ[M] L, - (X - C (⟨x_1 ↑x.gen, hin x_1⟩ : 𝒪[L])) = -1 * (X - C (⟨x_1 ↑x.gen, hin x_1⟩ : 𝒪[L])) := by
        intro t
        ring
      simp only [f, aux_11, ← neg_sub X, ugly, Finset.prod_mul_distrib, Finset.prod_const]
    simp only [neg_eq_iff_eq_neg] at ha
    simp only [ha, hb, sf, hmin]
    use (-1) * ((-1) ^ (⊤ : (Set (L ≃ₐ[M] L))).toFinset.card * eval x.gen (Polynomial.map e (Polynomial.map (algebraMap 𝒪[M] 𝒪[L]) h)))
    simp only [← Subring.coe_mul, Subtype.coe_inj, ← mul_assoc]
    conv =>
      enter [2, 1]
      rw [mul_comm]
    simp only [mul_assoc, eval_mul, hh, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_one, eval_pow, eval_neg, eval_one]
    conv =>
      enter [2, 1, 2]
      rw [mul_comm, mul_assoc]
      enter [2]
      rw [mul_assoc, ← pow_two, ← pow_mul, mul_comm _ 2, pow_mul, neg_one_pow_two, one_pow, mul_one]
    simp only [Subring.coe_mul, mul_neg, mul_one, NegMemClass.coe_neg, neg_inj]
    rw [mul_comm]
  simp only [a, b] at hdvd
  exact hdvd

theorem prop3
  (σ : M ≃ₐ[K] M) (x : PowerBasis 𝒪[K] 𝒪[L]) (y : PowerBasis 𝒪[K] 𝒪[M]) [Algebra.IsSeparable (IsLocalRing.ResidueField 𝒪[K]) (IsLocalRing.ResidueField 𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField 𝒪[M]) (IsLocalRing.ResidueField 𝒪[L])] :
    ∑ s ∈ ((restrictNormalHom M)⁻¹' {σ}), i_[L/K] s
    = (ramificationIdx M L) * i_[M/K] σ := by
  by_cases hσ : σ = .refl
  · subst hσ
    rw [lowerIndex_refl, ENat.mul_top]
    · have : (.refl : L ≃ₐ[K] L) ∈ (restrictNormalHom M)⁻¹' {.refl} := by
        rw [Set.mem_preimage, Set.mem_singleton_iff, ← AlgEquiv.aut_one, ← AlgEquiv.aut_one,
          _root_.map_one]
      rw [WithTop.sum_eq_top]
      exact ⟨.refl, Set.mem_toFinset.mpr this, lowerIndex_refl⟩
    · intro h
      rw [← ENat.coe_zero, ← ENat.some_eq_coe, WithTop.coe_eq_coe] at h
      apply ramificationIdx_ne_zero M L h
  · simp only [lowerIndex_of_powerBasis y, lowerIndex_of_powerBasis x]
    simp only [hσ, ↓reduceDIte]
    rw [← Finset.sum_attach]
    conv =>
      enter [1, 2]
      ext t
      simp only [preimage_nerefl σ hσ t.1 (Set.mem_toFinset.1 t.2), ↓reduceDIte]
    rw [← ENat.coe_mul, ← Nat.cast_sum]
    apply Nat.cast_inj.2
    rw [← Nat.cast_inj (R := ℤ), Nat.cast_sum]
    conv =>
      enter [1, 2]
      ext t
      rw [Int.toNat_of_nonneg (val_mappb_sub_self_toAdd_nonpos (preimage_nerefl σ hσ t.1 (Set.mem_toFinset.mp t.2)) x), ← toAdd_inv]
    conv_rhs =>
        rw [Nat.cast_mul, Int.toNat_of_nonneg (val_mappb_sub_self_toAdd_nonpos hσ y), mul_comm, ← toAdd_inv, ← Int.toAdd_pow, inv_pow]
    rw [← toAdd_prod]
    apply Equiv.congr_arg
    rw [Finset.prod_inv_distrib, inv_inj, ← WithZero.coe_inj, WithZero.coe_pow, WithZero.coe_unzero, WithZero.coe_prod]
    have hy1 : (σ y.gen - y.gen) ∈ vM.v.valuationSubring := by
      apply sub_mem
      · apply (mem_valuationSubring_iff v (σ ↑y.gen)).mpr
        rw [val_map_le_one_iff]
        exact SetLike.coe_mem y.gen
        exact algEquiv_preserve_val_of_complete σ
      · exact SetLike.coe_mem y.gen
    have hy2 : (⟨σ y.gen - y.gen, hy1⟩ : vM.v.valuationSubring) ≠ 0 := by
      apply Subtype.coe_ne_coe.1
      simp only [ZeroMemClass.coe_zero]
      by_contra hc
      absurd hσ
      rw [sub_eq_zero] at hc
      rw [eq_iff_ValuationSubring]
      apply PowerBasis.algHom_ext' y
      rw [← Subtype.val_inj, AlgEquiv.restrictValuationSubring_apply, AlgEquiv.restrictValuationSubring_apply, coe_refl, id_eq]
      exact hc
    simp only [WithZero.coe_unzero, Valuation.prolongs_by_ramificationIndex hy1 hy2, ← _root_.map_prod]
    obtain ⟨π, hpi⟩ := exists_isUniformizer_of_isDiscrete vL.v
    let a := (algebraMap M L) (σ ↑y.gen - ↑y.gen)
    let b := (∏ x_1 ∈ (⇑(restrictNormalHom M (K₁ := L)) ⁻¹' {σ}).toFinset.attach, (x_1.1 x.gen - x.gen))
    have hr1 : a ∈ v.valuationSubring := by
      simp only [a]
      refine (mem_valuationSubring_iff v ((algebraMap M L) (σ ↑y.gen - ↑y.gen))).mpr ?_
      simp only [IsValExtension.val_map_le_one_iff vM.v vL.v]
      apply (mem_valuationSubring_iff v ((σ ↑y.gen - ↑y.gen))).mp
      exact hy1
    have hr1' :  (⟨a, hr1⟩ : vL.v.valuationSubring) ≠ 0 := by
      apply Subtype.coe_ne_coe.1
      simp only [ZeroMemClass.coe_zero, a]
      apply (_root_.map_ne_zero (algebraMap M L)).mpr
      apply Subtype.coe_ne_coe.2 at hy2
      simp only [ZeroMemClass.coe_zero] at hy2
      exact hy2
    have hr2 : b ∈ v.valuationSubring := by
      simp only [b, mem_valuationSubring_iff, map_prod]
      apply Finset.prod_le_one
      exact fun i a ↦ WithZero.zero_le (v (i.1 ↑x.gen - ↑x.gen))
      intro i hi
      exact val_map_sub_le_one (mem_decompositionGroup i.1) x.gen
    have hr2' :  (⟨b, hr2⟩ : vL.v.valuationSubring) ≠ 0 := by
      apply Subtype.coe_ne_coe.1
      simp only [ZeroMemClass.coe_zero, b]
      apply Finset.prod_ne_zero_iff.2
      intro ⟨i, hi⟩ hi1
      by_contra hc
      nth_rw 2 [← id_eq x.gen] at hc
      rw [sub_eq_zero, ← coe_refl (R := 𝒪[K])] at hc
      have heq : i = .refl := by
        rw [eq_iff_ValuationSubring]
        apply PowerBasis.algHom_ext' x
        rw [← Subtype.val_inj, AlgEquiv.restrictValuationSubring_apply, AlgEquiv.restrictValuationSubring_apply]
        exact hc
      simp only [Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hi
      absurd hσ
      rw [← hi, heq]
      apply (restrictNormalHom M).map_one
    obtain ⟨n1, u1, hnu1⟩ := pow_uniformizer vL.v (r := ⟨a, hr1⟩) hr1' ⟨π, hpi⟩
    obtain ⟨n2, u2, hnu2⟩ := pow_uniformizer vL.v (r := ⟨b, hr2⟩) hr2' ⟨π, hpi⟩
    simp only [_root_.map_sub, SubmonoidClass.coe_pow, a, b] at hnu1 hnu2
    simp only [_root_.map_sub, hnu1, hnu2, _root_.map_mul, _root_.map_pow, val_valuationSubring_unit, mul_one]
    apply congrArg
    obtain ⟨s, hs⟩ := AlgEquiv.restrictNormalHom_surjective L σ
    let f := ∏ t ∈ (⊤ : Set (L ≃ₐ[K] L)).toFinset, (X - C (t x.gen))
    let e : L →+* L := {
      toFun := fun t => s t
      map_one' := map_one s
      map_mul' := AlgEquiv.map_mul' s
      map_zero' := map_zero s
      map_add' := AlgEquiv.map_add' s
    }
    let sf := Polynomial.map e f
    let sf' := ∏ t ∈ (⊤ : Set (L ≃ₐ[K] L)).toFinset, (X - C ((s * t) x.gen))
    have hcoeff : ∀ i : ℕ, coeff sf i = s (coeff f i) := by
      intro i
      simp only [sf, e, coeff_map, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    apply le_antisymm
    · have hab : ∃ t : 𝒪[L], a = b * t := by
        simp only [a, b]
        apply aux_2
      simp only [a, b, _root_.map_sub, hnu1, hnu2] at hab
      obtain ⟨t, ht⟩ := hab
      apply_fun vL.v at ht
      simp only [_root_.map_mul, _root_.map_pow] at ht
      rw [hpi, val_valuationSubring_unit, val_valuationSubring_unit, mul_one, mul_one] at ht
      simp only [← zpow_natCast, Int.reduceNeg, ofAdd_neg, WithZero.coe_inv, inv_zpow, ← WithZero.ofAdd_zpow n1, ← WithZero.ofAdd_zpow n2] at ht
      have hle : (↑(Multiplicative.ofAdd (n2 : ℤ))) ≤ (↑(Multiplicative.ofAdd (n1 : ℤ))) := by
        rw [← inv_le_inv_iff, ← WithZero.coe_le_coe, WithZero.coe_inv, ht]
        apply mul_le_of_le_one_right'
        apply (mem_valuationSubring_iff _ _).1 t.2
      rw [← Multiplicative.toAdd_le, toAdd_ofAdd, toAdd_ofAdd] at hle
      exact_mod_cast hle
    · have hab : ∃ t : 𝒪[L], b = a * t := by
        simp only [a, b]
        apply aux_1 σ hσ x
      simp only [a, b, _root_.map_sub, hnu1, hnu2] at hab
      obtain ⟨t, ht⟩ := hab
      apply_fun vL.v at ht
      simp only [_root_.map_mul, _root_.map_pow] at ht
      rw [hpi, val_valuationSubring_unit, val_valuationSubring_unit, mul_one, mul_one] at ht
      simp only [← zpow_natCast, Int.reduceNeg, ofAdd_neg, WithZero.coe_inv, inv_zpow, ← WithZero.ofAdd_zpow n1, ← WithZero.ofAdd_zpow n2] at ht
      have hle : (↑(Multiplicative.ofAdd (n1 : ℤ))) ≤ (↑(Multiplicative.ofAdd (n2 : ℤ))) := by
        rw [← inv_le_inv_iff, ← WithZero.coe_le_coe, WithZero.coe_inv, ht]
        apply mul_le_of_le_one_right'
        apply (mem_valuationSubring_iff _ _).1 t.2
      rw [← Multiplicative.toAdd_le, toAdd_ofAdd, toAdd_ofAdd] at hle
      exact_mod_cast hle
