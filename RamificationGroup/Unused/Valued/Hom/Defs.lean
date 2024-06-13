import RamificationGroup.Unused.Valued.Defs

/-!
# ValRingHom and ValAlgebra

In this file we define the type of ring homomorphisms that respect the valuation structure. We require such a homomorphism from valued ring `R` to valued ring `S` to satisfy the condition that the valuation on `R` is equivalent to the pullback of the valuation on `S`. This is strictly stronger than merely requiring `v x ≤ v y → v (f x) ≤ v (f y)`.

## Main definitions

* `ValRingHom` : Valued ring homomorphisms.
* `ValRingEquiv` : Valued ring isomorphisms.
* `ValAlgebra`
* `ValAlgHom`
* `ValAlgEquiv`

## Notations

* `→+*v`: Valued ring homomorphisms.
* `≃+*v`: Valued ring isomorphisms.
* `A →ₐv[R] B`
* `A ≃ₐv[R] B`

## Implementation notes


## Tags

valued ring homomorphism, valued homomorphism

-/

-- `Consider K → K [[X]] , K is a local field, K[X] with valuation trivial on K, valuation ideal given by (X). This satisfies v x ≤ v y → v f x ≤ v f y`
-- if the first definition K of local field K can have many valuation on L. second  will pin down the valuation on L
-- if as first choice, order preserving <=> valuation preserving <=> continuous (v(x) < 1 -> v f x < 1, by x^n -> 0 -> f x ^n -> 0)
-- preorder on the set of valuations? not a type, IsSpecialization

-- TODO : Split these into 3 files(?) .ValAlgebra.Hom, .ValAlgebra.Basic
-- TODO : SubValRing SubValAlgebra, SubValAlgebraClass, intermediate field shoul be SubValAlgebraClass instance.
-- Question : whether the order should be included as part of the data of Valued instance? not an instance derived from Valued.
-- TODO : Coe lemmas, how should they be arranged?
-- Not TODO : scalartower do not need a val version. [IsScalarTower R S T] + [ValAlgebra R S] + [ValAlgebra S T] contains enough information
-- TODO (?) : SubValRing gives ValAlgbra instance, what instance of valued should subalgebra be equipped? This always conflicts with DIscrete valuation in the local field case
open DiscreteValuation Valuation Valued

section ValRingHom_ValRingEquiv

section Hom

-- Valuation on B is an extension of valuation on A.
/-- `ValRingHom R S` is the type of ring homomorphisms that preserves valuation from valued ring `R` to valued ring `S`.

Please note that the definition requires `v x ≤ v y ↔ v (f x) ≤ v (f y)` instead of `v x ≤ v y → v (f x) ≤ v (f y)`. For the latter case, one can use order-preserving ring homomorphisms.

When possible, instead of parametrizing results over `(f : ValRingHom R S)`,
you should parametrize over `(F : Type*) [ValRingHomClass F R S] (f : F)`.

When you extend this structure, make sure to extend `ValRingHomClass`.
-/ -- mimicked from `OrderRingHom`
structure ValRingHom (R S : Type*) {ΓR ΓS : outParam Type*} [Ring R] [Ring S]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS]
  [vR : Valued R ΓR] [vS : Valued S ΓS]
  extends OrderRingHom R S, ContinuousMap R S where
  /-- The proposition that the ring map preserves valuation. -/
  val_isEquiv_comap' : vR.v.IsEquiv (vS.v.comap toRingHom)

/-- Reinterpret a valued ring homomorphism into a ordered ring homomorphism. -/
add_decl_doc ValRingHom.toOrderRingHom

attribute [coe] ValRingHom.toOrderRingHom

@[inherit_doc]
infixr:25 " →+*v " => ValRingHom -- 25 = Binding power of `→+*`

/-- `ValRingEquiv R S` is the type of ring isomorphisms that preserves valuation from valued ring `R` to valued ring `S`.

When possible, instead of parametrizing results over `(f : ValRingEquiv R S)`,
you should parametrize over `(F : Type*) [ValRingEquivClass F R S] (f : F)`.

When you extend this structure, make sure to extend `ValRingEquivClass`.
-/
structure ValRingEquiv (R S : Type*) {ΓR ΓS : outParam Type*} [Ring R] [Ring S]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS]
  [vR : Valued R ΓR] [vS : Valued S ΓS]
  extends OrderRingIso R S, Homeomorph R S where
  val_isEquiv_comap' : vR.v.IsEquiv (vS.v.comap toRingEquiv)

/-- Reinterpret a valued ring isomorphism into a ordered ring isomorphism. -/
add_decl_doc ValRingEquiv.toOrderRingIso

attribute [coe] ValRingEquiv.toOrderRingIso

@[inherit_doc]
infixr:25 " ≃+*v " => ValRingEquiv

end Hom

section Class

/-- `ValHomClass F R S` asserts that `F` is a type of valuation-preserving morphisms. -/
class ValRingHomClass (F R S : Type*) {ΓR ΓS : outParam Type*} [Ring R] [Ring S]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS]
  [vR : Valued R ΓR] [vS : Valued S ΓS] [FunLike F R S] extends RelHomClass F ((· ≤ ·) : R → R → Prop) ((· ≤ ·) : S → S → Prop), RingHomClass F R S, ContinuousMapClass F R S : Prop where
  val_isEquiv_comap (f : F) : vR.v.IsEquiv (vS.v.comap f)

export ValRingHomClass (val_isEquiv_comap)

class ValRingEquivClass (F R S : Type*) {ΓR ΓS : outParam Type*} [Ring R] [Ring S]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS]
  [vR : Valued R ΓR] [vS : Valued S ΓS] [EquivLike F R S] extends OrderIsoClass F R S, RingEquivClass F R S, ContinuousMapClass F R S : Prop where
  inv_continuous (f : F) : Continuous (EquivLike.inv f)
  val_isEquiv_comap (f : F) : vR.v.IsEquiv (vS.v.comap f)

variable {F R S : Type*} {ΓR ΓS : outParam Type*} [Ring R] [Ring S]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS]
  [vR : Valued R ΓR] [vS : Valued S ΓS]

/-- Turn an element of a type `F` satisfying `ValRingHomClass F R S` into an actual
`ValRingHom`. This is declared as the default coercion from `F` to `R →+*v S`. -/
@[coe]
def ValRingHomClass.toValRingHom [FunLike F R S] [ValRingHomClass F R S] (f : F) :
    R →+*v S :=
  { OrderHomClass.toOrderHom f, RingHomClass.toRingHom f, toContinuousMap f with val_isEquiv_comap' := ValRingHomClass.val_isEquiv_comap f}

/-- Any type satisfying `ValRingHomClass` can be cast into `ValRingHom` via
`ValRingHomClass.toValRingHom`. -/
instance [FunLike F R S] [ValRingHomClass F R S] : CoeTC F (R →+*v S) :=
  ⟨ValRingHomClass.toValRingHom⟩

/-- Turn an element of a type `F` satisfying `ValRingEquivClass F R S` into an actual
`ValRingEquiv`. This is declared as the default coercion from `F` to `R ≃+*v S`. -/
@[coe]
def ValRingEquivClass.toValRingEquiv [EquivLike F R S] [ValRingEquivClass F R S] (f : F) :
    R ≃+*v S :=
  { OrderIsoClass.toOrderIso f, RingEquivClass.toRingEquiv f, toContinuousMap f with
    val_isEquiv_comap' := ValRingEquivClass.val_isEquiv_comap f
    map_le_map_iff' := map_le_map_iff f
    continuous_invFun := ValRingEquivClass.inv_continuous f
    }

/-- Any type satisfying `ValRingHomClass` can be cast into `ValRingHom` via
`ValRingHomClass.toValRingHom`. -/
instance [FunLike F R S] [ValRingHomClass F R S] : CoeTC F (R →+*v S) :=
  ⟨ValRingHomClass.toValRingHom⟩

/-- Any type satisfying `ValRingEquivClass` can be cast into `ValRingEquiv` via
`ValRingEquivClass.toValRingEquiv`. -/
instance [EquivLike F R S] [ValRingEquivClass F R S] : CoeTC F (R ≃+*v S) :=
  ⟨ValRingEquivClass.toValRingEquiv⟩

-- See note [lower instance priority]
instance (priority := 100) ValRingEquivClass.toValRingHomClass
    [EquivLike F R S] [ValRingEquivClass F R S] : ValRingHomClass F R S :=
  { OrderIsoClass.toOrderHomClass with
    val_isEquiv_comap := ValRingEquivClass.val_isEquiv_comap }

section Hom

variable [FunLike F R S] [ValRingHomClass F R S]

@[simp]
theorem val_map_le_iff (f : F) {x y : R} : v (f x) ≤ v (f y) ↔ v x ≤ v y := (val_isEquiv_comap f x y).symm

@[simp]
theorem val_map_lt_iff (f : F) {x y : R} : v (f x) < v (f y) ↔ v x < v y := by
  convert (val_map_le_iff f).not <;>
  push_neg <;> rfl

@[simp]
theorem val_map_le_one_iff (f : F) {x : R} : v (f x) ≤ 1 ↔ v x ≤ 1 := by
  convert val_map_le_iff f (x := x) (y := 1) <;>
  simp only [_root_.map_one]

@[simp]
theorem val_map_lt_one_iff (f : F) {x : R} : v (f x) < 1 ↔ v x < 1 := by
  convert val_map_lt_iff f (x := x) (y := 1) <;>
  simp only [_root_.map_one]

end Hom

section Equiv

variable [EquivLike F R S] [ValRingEquivClass F R S]

@[simp]
theorem val_map_inv_le_val_iff (f : F) {x : R} {y : S} : v (EquivLike.inv f y) ≤ v x ↔ v y ≤ v (f x) := by
  convert (val_map_le_iff f).symm
  exact (EquivLike.right_inv f _).symm

@[simp]
theorem val_le_val_map_inv_iff (f : F) {x : R} {y : S} : v x ≤ v (EquivLike.inv f y) ↔ v (f x) ≤ v y := by
  convert (val_map_le_iff f).symm
  exact (EquivLike.right_inv _ _).symm

@[simp]
theorem val_map_inv_lt_val_iff (f : F) {x : R} {y : S} : v (EquivLike.inv f y) < v x ↔ v y < v (f x) := by
  convert (val_le_val_map_inv_iff f (x := x) (y := y)).not <;>
  push_neg <;> rfl

@[simp]
theorem val_lt_val_map_inv_iff (f : F) {x : R} {y : S} : v x < v (EquivLike.inv f y) ↔ v (f x) < v y := by
  convert (val_map_inv_le_val_iff f (x := x) (y := y)).not <;>
  push_neg <;> rfl

end Equiv

end Class

variable {R S T: Type*} {ΓR ΓS ΓT : outParam Type*}
  [Ring R] [Ring S] [Ring T]
  [LinearOrderedCommGroupWithZero ΓR]
  [LinearOrderedCommGroupWithZero ΓS]
  [LinearOrderedCommGroupWithZero ΓT]
  [vR : Valued R ΓR] [vS : Valued S ΓS] [vT : Valued T ΓT]

section HomIsClass

instance : FunLike (ValRingHom R S) R S where
  coe f := f.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨_, _⟩, _⟩
    rcases g with ⟨⟨_, _⟩, _⟩
    dsimp at h
    congr
    apply DFunLike.coe_injective' h

instance : ValRingHomClass (ValRingHom R S) R S where
  map_rel f _ _ h:= f.monotone' h
  map_mul f := f.map_mul
  map_one f := f.map_one
  map_add f := f.map_add
  map_zero f := f.map_zero
  map_continuous f := f.toContinuousMap.continuous_toFun
  val_isEquiv_comap f := f.val_isEquiv_comap'

instance : EquivLike (ValRingEquiv R S) R S where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h _ := by
    rcases f with ⟨⟨_, _⟩, _⟩
    rcases g with ⟨⟨_, _⟩, _⟩
    dsimp at h
    congr
    apply DFunLike.coe_injective' h

instance : ValRingEquivClass (ValRingEquiv R S) R S where
  map_le_map_iff f := f.map_le_map_iff'
  map_mul f := f.map_mul
  map_add f := f.map_add
  map_continuous f := f.toHomeomorph.continuous_toFun
  inv_continuous f := f.toHomeomorph.continuous_invFun
  val_isEquiv_comap f := f.val_isEquiv_comap'

end HomIsClass

section coe_and_lemma

-- `How should one organize coe lemmas???`
namespace ValRingHom

-- theorem val_isEquiv_comap (R S : Type*) {ΓR ΓS : outParam Type*} [Ring R] [Ring S]
--   [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS]
--   [vR : Valued R ΓR] [vS : Valued S ΓS] (f : R →+*v S) : vR.v.IsEquiv (vS.v.comap f) := f.val_isEquiv_comap'

-- @[simp]
-- theorem toOrderRingHom_eq_coe (f : R →+*v S) : f.toOrderRingHom = f := rfl

-- @[simp]
-- theorem toFun_eq_coe (f : R →+*v S) : f.toFun = f := rfl

@[ext]
theorem ext {f g : R →+*v S} (h : (f : R → S) = g) : f = g := DFunLike.coe_injective h

-- @[simp]
-- theorem coe_eq (f : R →+*v S) : ValRingHomClass.toValRingHom f = f := rfl

end ValRingHom

-- @[simp]
-- theorem ValRingHomClass.coe_coe {F} [FunLike F R S] [ValRingHomClass F R S] (f : F) : ⇑(f : R →+*v S) = f := rfl

-- @[simp]
-- theorem ValRingHomClass.coe_toOrderRingIso {F} [FunLike F R S] [ValRingHomClass F R S] (f : F) : ⇑(f : R →+*o S) = f := rfl

namespace ValRingEquiv

-- @[simp]
-- theorem toFun_eq_coe (f : R ≃+*v S) : f.toFun = f := rfl

-- @[simp]
-- theorem toRingEquiv_toOrderRingIso_eq_coe (f : R ≃+*v S) : ((f.toOrderRingIso) : R ≃+* S) = f := rfl

-- @[simp]
-- theorem coe_toOrderRingIso_eq_coe (f : R ≃+*v S) : ⇑(f.toOrderRingIso) = f := rfl

@[ext]
theorem ext (f g : R ≃+*v S) (h : (f : R → S) = g) : f = g := DFunLike.coe_injective h

theorem bijective (f : R ≃+*v S) : Function.Bijective f := f.toEquiv.bijective

theorem injective (f : R ≃+*v S) : Function.Injective f := f.toEquiv.injective

theorem surjective (f : R ≃+*v S) : Function.Surjective f := f.toEquiv.surjective

-- @[simp]
-- theorem coe_eq (f : R ≃+*v S) : ValRingEquivClass.toValRingEquiv f = f := rfl

end ValRingEquiv

-- @[simp]
-- theorem ValRingEquivClass.coe_coe {F} [EquivLike F R S] [ValRingEquivClass F R S] (f : F) : ⇑(f : R ≃+*v S) = f := rfl

-- @[simp]
-- theorem ValRingEquivClass.coe_toOrderRingIso {F} [EquivLike F R S] [ValRingEquivClass F R S] (f : F) : ⇑(f : R ≃+*o S) = f := rfl

/- ` Add these `
Low TODO : canlift

Low TODO :coe simp lemmas, such as

toOrderRingIso coe_mk coe_mk' toFun_eq_coe

How should these coe lemma be organized??

`refl symm trans group`
-/

end coe_and_lemma

section mk'

theorem map_le_map_iff_of_val_isEquiv_comap {f : R ≃+* S} {x y : R} (hf : vR.v.IsEquiv (vS.v.comap f)) : f x ≤ f y ↔ x ≤ y := by
    rw [le_iff_val_le, le_iff_val_le]
    exact (hf x y).symm

theorem monotone_of_val_isEquiv_comap {f : R →+* S} (hf : vR.v.IsEquiv (vS.v.comap f)) : Monotone f := by
  intro x y h
  rw [le_iff_val_le] at h ⊢
  exact (hf x y).1 h

-- to Mathlib Mathlib.Topology.Algebra.Valuation
theorem Valued.mem_nhds' {R : Type*}  [Ring R]  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]  [_i : Valued R Γ₀] {s : Set R} {x : R} :
s ∈ nhds x ↔ ∃ (a : R), Valued.v a > 0 ∧ {y : R | Valued.v (y - x) < Valued.v a} ⊆ s := sorry

theorem continuous_of_val_isEquiv_comap {f : R →+* S} (hf : vR.v.IsEquiv (vS.v.comap f)) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  simp [ContinuousAt, Filter.Tendsto, Filter.map]
  intro s
  simp
  rw [Valued.mem_nhds', Valued.mem_nhds']
  rintro ⟨a, ⟨ha, h⟩⟩
  -- use a
  sorry -- difficult

-- lower TODO : stronger version, f is topological embedding

protected theorem val_isEquiv_comap.symm {f : R ≃+* S} (hf : vR.v.IsEquiv (vS.v.comap f)) : vS.v.IsEquiv (vR.v.comap f.symm) := by
  intro x y
  convert (hf (f.invFun x) (f.invFun y)).symm <;>
  simp only [RingEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, comap_apply, RingHom.coe_coe,
    EquivLike.apply_coe_symm_apply]

def ValRingHom.mk' {f : R →+* S} (hf : vR.v.IsEquiv (vS.v.comap f)) : R →+*v S where
  toRingHom := f
  monotone' := monotone_of_val_isEquiv_comap hf
  val_isEquiv_comap' := hf
  continuous_toFun := continuous_of_val_isEquiv_comap hf

def ValRingEquiv.mk' {f : R ≃+* S} (hf : vR.v.IsEquiv (vS.v.comap f)) : R ≃+*v S where
  toRingEquiv := f
  map_le_map_iff' := map_le_map_iff_of_val_isEquiv_comap hf
  continuous_toFun := continuous_of_val_isEquiv_comap hf
  continuous_invFun := continuous_of_val_isEquiv_comap (val_isEquiv_comap.symm hf)
  val_isEquiv_comap' := hf

-- TODO: coe lemmas of mk', @[simp]

end mk'

section Composition

namespace ValRingHom

variable (R) in
/-- The identity function as bundled valuation ring homomorphism. -/
def id : R →+*v R :=
  ⟨.id R, continuous_id , IsEquiv.refl⟩

instance : Inhabited (R →+*v R) := ⟨ ValRingHom.id R ⟩

@[simp]
theorem id_apply (r : R) : ValRingHom.id R r = r := rfl

def comp (g : S →+*v T) (f : R →+*v S) : R →+*v T where
  toOrderRingHom := (↑g : OrderRingHom S T).comp f
  continuous_toFun := by
    simp only [OrderRingHom.comp]
    dsimp
    exact Continuous.comp g.continuous_toFun f.continuous_toFun
  val_isEquiv_comap' := by
    intro x y
    convert f.val_isEquiv_comap' x y
    exact (g.val_isEquiv_comap' (f x) (f y)).symm

@[simp]
theorem id_comp (f : R →+*v S) : (ValRingHom.id S).comp f = f := by
  ext
  rfl

@[simp]
theorem comp_id (f : R →+*v S) : f.comp (.id R) = f := by
  ext
  rfl

end ValRingHom

namespace ValRingEquiv

variable (R) in
/-- Identity valued ring isomorphism. -/
@[refl]
def refl : (R ≃+*v R) where
  toOrderRingIso := .refl R
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id
  val_isEquiv_comap' := IsEquiv.refl

@[simp]
theorem coe_refl : (refl R : R →+*v R) = .id R :=
  rfl

@[simp]
theorem refl_apply (x : R) : refl R x = x :=
  rfl

@[simp]
theorem refl_toEquiv : (refl R).toEquiv = Equiv.refl R :=
  rfl

/-- Inverse of an valued ring isomorphism. -/
def symm (f : R ≃+*v S) : S ≃+*v R where
  toOrderRingIso := OrderRingIso.symm f
  continuous_toFun := f.continuous_invFun
  continuous_invFun := f.continuous_toFun
  val_isEquiv_comap' := by
    intro x y
    convert IsEquiv.symm (val_isEquiv_comap f) (f.invFun x) (f.invFun y) <;>
    simp only [comap_apply] <;>
    congr <;>
    exact (f.right_inv _).symm

@[simp]
theorem apply_symm_apply (f : R ≃+*v S) (x : S) : f (f.symm x) = x :=
  f.toEquiv.apply_symm_apply x

@[simp]
theorem symm_apply_apply (f : R ≃+*v S) (x : R) : f.symm (f x) = x :=
  f.toEquiv.symm_apply_apply x

@[simp]
theorem symm_refl : (ValRingEquiv.refl R).symm = .refl R := rfl

theorem apply_eq_iff_eq_symm_apply (f : R ≃+*v S) (x : R) (y : S) : f x = y ↔ x = f.symm y :=
  f.toEquiv.apply_eq_iff_eq_symm_apply

theorem symm_apply_eq (f : R ≃+*v S) {x : R} {y : S} : f.symm y = x ↔ y = f x :=
  f.toEquiv.symm_apply_eq

@[simp]
theorem symm_symm (f : R ≃+*v S) : f.symm.symm = f := rfl

theorem symm_bijective : Function.Bijective (.symm : (R ≃+*v S) → S ≃+*v R) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

theorem symm_injective : Function.Injective (.symm : (R ≃+*v S) → S ≃+*v R) :=
  symm_bijective.injective

theorem symm_surjective : Function.Surjective (.symm : (R ≃+*v S) → S ≃+*v R) :=
  symm_bijective.surjective

@[simp]
theorem toEquiv_symm (f : R ≃+*v S) : f.toEquiv.symm = f.symm.toEquiv :=
  rfl

/-- Composition of two valued ring isomorphisms is an order isomorphism. -/
@[trans]
def trans (f : R ≃+*v S) (f' : S ≃+*v T) : R ≃+*v T where -- trans has different order comparing with comp
  toOrderRingIso := OrderRingIso.trans (β := S) f f'
  continuous_toFun := by
    apply Continuous.comp (Y := S)
    exact f'.continuous_toFun
    exact f.continuous_toFun
  continuous_invFun := by
    apply Continuous.comp (Y := S)
    exact f.continuous_invFun
    exact f'.continuous_invFun
  val_isEquiv_comap' := by
    intro x y
    convert f.val_isEquiv_comap' x y
    exact (f'.val_isEquiv_comap' (f x) (f y)).symm

@[simp]
theorem coe_trans (e : R ≃+*v S) (e' : S ≃+*v T) : ⇑(e.trans e') = e' ∘ e :=
  rfl

@[simp]
theorem trans_apply (e : R ≃+*v S) (e' : S ≃+*v T) (x : R) : e.trans e' x = e' (e x) :=
  rfl

@[simp]
theorem refl_trans (e : R ≃+*v S) : (refl R).trans e = e := by
  ext x
  rfl

@[simp]
theorem trans_refl (e : R ≃+*v S) : e.trans (refl S) = e := by
  ext x
  rfl

@[simp]
theorem symm_trans_apply (e₁ : R ≃+*v S) (e₂ : S ≃+*v T) (c : T) :
    (e₁.trans e₂).symm c = e₁.symm (e₂.symm c) :=
  rfl

theorem symm_trans (e₁ : R ≃+*v S) (e₂ : S ≃+*v T) : (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl

@[simp]
theorem symm_trans_self (e : R ≃+*v S) : e.trans e.symm = .refl R := by
  ext; apply Equiv.left_inv

@[simp]
theorem self_symm_trans (e : R ≃+*v S) : e.symm.trans e = .refl S := by
  ext; apply Equiv.right_inv

-- -- structures on ValRingIso
instance group : Group (R ≃+*v R) where
  mul e e' := e'.trans e
  mul_assoc := by intros; rfl
  one := .refl R
  one_mul := by intros; rfl
  mul_one := by intros; rfl
  inv := .symm
  mul_left_inv := symm_trans_self

@[simp]
theorem one_apply (x : R) : (1 : R ≃+*v R) x = x := rfl

@[simp]
theorem mul_apply (e e' : (R ≃+*v R)) (x : R) : (e * e') x = e (e' x) := rfl

end ValRingEquiv

end Composition

end ValRingHom_ValRingEquiv

section ValAlgebra

/-- A valued algebra over a valued commutative ring `R`, is a valued ring `A` together with a ring map into the center of `A` that preserves the valuation.-/
class ValAlgebra (R A : Type*) {ΓR ΓA : outParam Type*} [CommRing R] [Ring A] [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [vR : Valued R ΓR] [vA : Valued A ΓA] extends ValRingHom R A, Algebra R A

/-- The valued ring homomorphism `R →+*v A` given by `Algebra` structure. -/
def valAlgebraMap (R A : Type*) {ΓR ΓA : outParam Type*} [CommRing R] [Ring A] [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [Valued R ΓR] [Valued A ΓA] [ValAlgebra R A] : R →+*v A := ValAlgebra.toValRingHom

variable {R A : Type*} {ΓR ΓA : outParam Type*} [CommRing R] [Ring A] [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [vR : Valued R ΓR] [vA : Valued A ΓA] [ValAlgebra R A]

-- Please do not use this in general, it has definitional equal problems.
/-- Creating a valued algebra from a valued ring morphism. -/
def ValRingHom.toValAlgebra' (f : R →+*v A) (h : ∀ (c : R) (x : A), f c * x = x * f c): ValAlgebra R A where
  toValRingHom := f
  smul := (f.toAlgebra' h).smul
  smul_def' := (f.toAlgebra' h).smul_def'
  commutes' := (f.toAlgebra' h).commutes'

def ValRingHom.toValAlgebra {R A : Type*} {ΓR ΓA : outParam Type*} [CommRing R] [CommRing A] [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [Valued R ΓR] [Valued A ΓA] (f : R →+*v A) : ValAlgebra R A :=
  f.toValAlgebra' (fun _ => mul_comm _)

theorem ValRingHom.valAlgebraMap_toValAlgebra {R A : Type*} {ΓR ΓA : outParam Type*} [CommRing R] [CommRing A] [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [Valued R ΓR] [Valued A ΓA] [ValAlgebra R A] (f : R →+*v A) :
    @valAlgebraMap R A _ _ _ _ _ _ _ _ f.toValAlgebra  = f :=
  rfl

namespace ValAlgebra

/-- To prove two valued algebra structures on a fixed `[CommRing R] [Ring A]` agree,
it suffices to check the `algebraMap`s agree.
-/
@[ext]
theorem valAlgebra_ext (P Q : ValAlgebra R A)
    (h : ∀ r : R, (haveI := P; valAlgebraMap R A r) = haveI := Q; valAlgebraMap R A r) :
    P = Q := by
  replace h : P.toRingHom = Q.toRingHom := DFunLike.ext _ _ h
  have h' : (haveI := P; (· • ·) : R → A → A) = (haveI := Q; (· • ·) : R → A → A) := by
    funext r a
    rw [P.smul_def', Q.smul_def', h]
  rcases P with @⟨⟨⟨P⟩⟩, ⟨PSmul⟩⟩
  rcases Q with @⟨⟨⟨Q⟩⟩, ⟨QSmul⟩⟩
  congr

theorem val_isEquiv_comap : vR.v.IsEquiv (vA.v.comap (algebraMap R A)) :=
  (valAlgebraMap R A).val_isEquiv_comap'

open algebraMap

@[simp]
theorem val_map_le_iff (x y : R) : v (x : A) ≤ v (y : A) ↔ v x ≤ v y :=
  _root_.val_map_le_iff (valAlgebraMap R A)

@[simp]
theorem val_map_lt_iff (x y : R) : v (x : A) < v (y : A) ↔ v x < v y :=
  _root_.val_map_lt_iff (valAlgebraMap R A)

@[simp]
theorem val_map_le_one_iff (x : R) : v (x : A) ≤ 1 ↔ v x ≤ 1 :=
  _root_.val_map_le_one_iff (valAlgebraMap R A)

@[simp]
theorem val_map_lt_one_iff (x : R) : v (x : A) < 1 ↔ v x < 1 :=
  _root_.val_map_lt_one_iff (valAlgebraMap R A)

variable (R) in
/-- The identity map inducing an `ValAlgebra` structure. -/
instance id : ValAlgebra R R where
  -- copied from `Algebra.id`
  -- We override `toFun` and `toSMul` because `ValRingHom.id` is not reducible and cannot
  -- be made so without a significant performance hit.
  -- see library note [reducible non-instances].
  toFun x := x
  toSMul := Mul.toSMul _
  __ := ValRingHom.toValAlgebra (ValRingHom.id R)

namespace id

@[simp]
theorem map_eq_id : valAlgebraMap R R = ValRingHom.id R :=
  rfl

theorem map_eq_self (x : R) : valAlgebraMap R R x = x :=
  rfl

end id

end ValAlgebra

end ValAlgebra

section ValAlgHom_ValAlgEquiv

section Hom

variable (R A B : Type*) [CommRing R] [Ring A] [Ring B] {ΓR ΓA ΓB : outParam Type*} [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [LinearOrderedCommGroupWithZero ΓB] [Valued R ΓR] [vA : Valued A ΓA] [vB : Valued B ΓB] [ValAlgebra R A] [ValAlgebra R B]

/-- Defining the homomorphism in the category of valued-`R`-algebra. -/
structure ValAlgHom extends ValRingHom A B, AlgHom R A B

/-- Defining the isomorphism in the category of valued-`R`-algebra. -/
structure ValAlgEquiv extends ValRingEquiv A B, AlgEquiv R A B

/-- Reinterpret an `ValAlgHom` as a `ValRingHom` -/
add_decl_doc ValAlgHom.toValRingHom
attribute [coe] ValAlgHom.toValRingHom

/-- Reinterpret an `ValAlgHom` as a `AlgHom` -/
add_decl_doc ValAlgHom.toAlgHom
attribute [coe] ValAlgHom.toAlgHom

/-- Reinterpret an `ValAlgEquiv` as a `ValRingEquiv` -/
add_decl_doc ValAlgEquiv.toValRingEquiv
attribute [coe] ValAlgEquiv.toValRingEquiv

/-- Reinterpret an `ValAlgEquiv` as a `AlgEquiv` -/
add_decl_doc ValAlgEquiv.toAlgEquiv
attribute [coe] ValAlgEquiv.toAlgEquiv

@[inherit_doc]
notation:25 A " →ₐv[" R "] " B => ValAlgHom R A B

@[inherit_doc]
notation:25 A " ≃ₐv[" R "] " B => ValAlgEquiv R A B

end Hom

variable {R A B C D: Type*} [CommRing R] [Ring A] [Ring B] [Ring C] [Ring D]
{ΓR ΓA ΓB ΓC ΓD: outParam Type*} [LinearOrderedCommGroupWithZero ΓR]
[LinearOrderedCommGroupWithZero ΓA] [LinearOrderedCommGroupWithZero ΓB]
[LinearOrderedCommGroupWithZero ΓC]
[LinearOrderedCommGroupWithZero ΓD]
[Valued R ΓR] [vA : Valued A ΓA] [vB : Valued B ΓB] [vC : Valued C ΓC] [vD : Valued D ΓD]
[fA : ValAlgebra R A] [fB : ValAlgebra R B] [fC : ValAlgebra R C] [fD : ValAlgebra R D]

section Class

/-- `ValAlgHomClass F R A B` asserts `F` is a type of bundled valued algebra homomorphisms
from `A` to `B`.  -/
class ValAlgHomClass (F : Type*) (R A B : outParam Type*) [CommRing R] [Ring A] [Ring B]
  {ΓR ΓA ΓB : outParam Type*} [LinearOrderedCommGroupWithZero ΓR]
  [LinearOrderedCommGroupWithZero ΓA] [LinearOrderedCommGroupWithZero ΓB]
  [Valued R ΓR] [vA : Valued A ΓA] [vB : Valued B ΓB] [ValAlgebra R A] [ValAlgebra R B]
  [FunLike F A B] extends ValRingHomClass F A B, AlgHomClass F R A B : Prop

instance : FunLike (A →ₐv[R] B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨_, _⟩, _⟩
    rcases g with ⟨⟨_, _⟩, _⟩
    dsimp at h
    congr
    apply DFunLike.coe_injective'
    exact h

instance : EquivLike (A ≃ₐv[R] B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h _ := by
    rcases f with ⟨⟨_, _⟩, _⟩
    rcases g with ⟨⟨_, _⟩, _⟩
    dsimp at h
    congr
    apply DFunLike.coe_injective'
    exact h

instance (priority := 100) : ValRingHomClass (A →ₐv[R] B) A B where
  map_rel f := map_rel f.toValRingHom
  map_mul f := f.map_mul
  map_one f := f.map_one
  map_add f := f.map_add
  map_zero f := f.map_zero
  map_continuous f := f.toValRingHom.continuous_toFun
  val_isEquiv_comap f := f.val_isEquiv_comap'

instance (priority := 100) : ValRingEquivClass (A ≃ₐv[R] B) A B where
  map_le_map_iff f := map_le_map_iff f.toValRingEquiv
  map_mul f := f.map_mul
  map_add f := f.map_add
  map_continuous f := f.toValRingEquiv.continuous_toFun
  inv_continuous f := f.toValRingEquiv.continuous_invFun
  val_isEquiv_comap f := f.val_isEquiv_comap'

instance (priority := 100) : AlgHomClass (A →ₐv[R] B) R A B :=
{
  commutes := fun f => f.commutes'
}

instance (priority := 100) : AlgEquivClass (A ≃ₐv[R] B) R A B :=
{
  commutes := fun f => f.commutes'
}

@[coe]
def ValAlgHom.ofAlgHomClassValRingHomClass {F : Type*}
  [FunLike F A B] [ValRingHomClass F A B] [AlgHomClass F R A B] (f : F) :
    A →ₐv[R] B :=
  { ValRingHomClass.toValRingHom f, AlgHomClass.toAlgHom f with}

instance (priority := 100) {F : Type*}
  [FunLike F A B] [ValRingHomClass F A B] [AlgHomClass F R A B] :
  CoeTC F (A →ₐv[R] B) where
    coe := ValAlgHom.ofAlgHomClassValRingHomClass

end Class

section coe

namespace ValAlgHom
-- copy AlgHom.coe_coe, ...
-- ..., coe_fn_injective

@[ext]
theorem ext {f g : A →ₐv[R] B} (h : (f : A → B) = g) : f = g := DFunLike.coe_injective h

end ValAlgHom

theorem comp_valAlgebraMap {F} [FunLike F A B] [FunLike F A B] [ValRingHomClass F A B] [AlgHomClass F R A B] (φ : F) : (φ : A →+*v B).comp (valAlgebraMap R A) = valAlgebraMap R B :=
  DFunLike.ext _ _ <| AlgHomClass.commutes φ

namespace ValAlgEquiv

@[ext]
theorem ext {f g : A ≃ₐv[R] B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

end ValAlgEquiv

end coe

namespace ValAlgHom

def mk' (f : A →ₐ[R] B) (h : vA.v.IsEquiv (vB.v.comap f)) : A →ₐv[R] B where
  toFun := f
  map_one' := f.map_one
  map_mul' := f.map_mul
  map_zero' := f.map_zero
  map_add' := f.map_add'
  monotone' := monotone_of_val_isEquiv_comap h
  val_isEquiv_comap' := h
  commutes' := f.commutes'
  continuous_toFun := continuous_of_val_isEquiv_comap h

theorem coe_mk' (f : A →ₐ[R] B) (h : vA.v.IsEquiv (vB.v.comap f)) : (mk' f h) = f := rfl

-- def mk'' : given ValRingHom and commute.
-- theorem coe_mk''

variable (R A) in
/-- Identity map as an `ValAlgHom`. -/
protected def id : (A →ₐv[R] A) where
  toOrderRingHom := .id A
  continuous_toFun := continuous_id
  val_isEquiv_comap' := IsEquiv.refl
  commutes' _ := rfl

@[simp]
theorem coe_id : ⇑(ValAlgHom.id R A) = id :=
  rfl

@[simp]
theorem id_toValRingHom : (ValAlgHom.id R A : A →+* A) = ValRingHom.id A :=
  rfl

@[simp]
theorem id_apply (p : A) : ValAlgHom.id R A p = p :=
  rfl

protected def comp (φ₁ : B →ₐv[R] C) (φ₂ : A →ₐv[R] B) : A →ₐv[R] C :=
  { φ₁.toValRingHom.comp ↑φ₂ with
    commutes' := fun r : R => by rw [← (φ₁ : B →ₐ[R] C).commutes', ← (φ₂ : A →ₐ[R] B).commutes]; rfl }

@[simp]
theorem coe_comp (φ₁ : B →ₐv[R] C) (φ₂ : A →ₐv[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂ :=
  rfl

theorem comp_apply (φ₁ : B →ₐv[R] C) (φ₂ : A →ₐv[R] B) (p : A) : φ₁.comp φ₂ p = φ₁ (φ₂ p) :=
  rfl

theorem comp_toRingHom (φ₁ : B →ₐv[R] C) (φ₂ : A →ₐv[R] B) :
    (φ₁.comp φ₂ : A →+*v C) = (φ₁ : B →+*v C).comp ↑φ₂ :=
  rfl

@[simp]
theorem comp_id (φ : A →ₐv[R] B) : φ.comp (ValAlgHom.id R A) = φ := by
  ext
  rfl

@[simp]
theorem id_comp (φ : A →ₐv[R] B) : (ValAlgHom.id R B).comp φ = φ := by
  ext
  rfl

theorem comp_assoc (φ₁ : C →ₐv[R] D) (φ₂ : B →ₐv[R] C) (φ₃ : A →ₐv[R] B) :
    (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) := by
  ext
  rfl

-- instance : Monoid (A →ₐv[R] A)

-- /-- `AlgebraMap` as an `AlgHom`. -/
-- def ofId : R →ₐv[R] A :=

end ValAlgHom

namespace ValAlgEquiv

def mk' (f : A ≃ₐ[R] B) (h : vA.v.IsEquiv (vB.v.comap f)) : A ≃ₐv[R] B :=
  { f, ValRingEquiv.mk' h with
  commutes' := f.commutes'
  }
theorem coe_mk' (f : A ≃ₐ[R] B) (h : vA.v.IsEquiv (vB.v.comap f)) : (mk' f h) = f := rfl

@[refl]
def refl : (A ≃ₐv[R] A) where
  toValRingEquiv := .refl A
  commutes' _ := rfl

instance : Inhabited (A ≃ₐv[R] A) :=
  ⟨.refl⟩

@[simp]
theorem refl_toAlgHom : ↑(.refl : A ≃ₐv[R] A) = AlgHom.id R A :=
  rfl

@[simp]
theorem coe_refl : ⇑(.refl : A ≃ₐv[R] A) = id :=
  rfl

/-- Inverse of a valued ring algebra equivalence. -/
@[symm]
def symm (e : A ≃ₐv[R] B) : B ≃ₐv[R] A :=
  { e.toValRingEquiv.symm with
    commutes' := fun r => by
      rw [← e.toRingEquiv.symm_apply_apply (algebraMap R A r)]
      congr
      change _ = e _
      exact ((e : A →ₐ[R] B).commutes r).symm }


@[simp]
theorem symm_toEquiv_eq_symm {e : A ≃ₐv[R] B} : (e : A ≃ B).symm = e.symm :=
  rfl

theorem invFun_eq_symm {e : A ≃ₐv[R] B} : e.invFun = e.symm :=
  rfl

@[simp]
theorem symm_symm (e : A ≃ₐv[R] B) : e.symm.symm = e := by
  ext
  rfl

theorem symm_bijective : Function.Bijective (symm : (A ≃ₐv[R] B) → B ≃ₐv[R] A) :=
  Function.bijective_iff_has_inverse.mpr ⟨_ , symm_symm, symm_symm⟩


@[simp]
theorem refl_symm : (.refl : A ≃ₐv[R] A).symm = .refl :=
  rfl

@[simp]
theorem toRingEquiv_symm (f : A ≃ₐv[R] A) : (f : A ≃+*v A).symm = f.symm :=
  rfl

@[simp]
theorem symm_toRingEquiv (e : A ≃ₐv[R] B): (e.symm : B ≃+*v A) = (e : A ≃+*v B).symm :=
  rfl

/-- Algebra equivalences are transitive. -/
@[trans]
def trans (e₁ : A ≃ₐv[R] B) (e₂ : B ≃ₐv[R] C) : A ≃ₐv[R] C :=
  { e₁.toValRingEquiv.trans e₂.toValRingEquiv with
    commutes' := fun r => show e₂.toFun (e₁.toFun _) = _ by rw [e₁.commutes', e₂.commutes'] }

@[simp]
theorem apply_symm_apply (e : A ≃ₐv[R] B) : ∀ x, e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : A ≃ₐv[R] B) : ∀ x, e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply

@[simp]
theorem self_symm_trans (e : A ≃ₐv[R] B) : e.symm.trans e = .refl := by
  ext x
  exact e.apply_symm_apply x

@[simp]
theorem symm_trans_self (e : A ≃ₐv[R] B) : e.trans e.symm = .refl := by
  ext x
  exact e.symm_apply_apply x

@[simp]
theorem symm_trans_apply (e₁ : A ≃ₐv[R] B) (e₂ : B ≃ₐv[R] C) (x : C) :
    (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
  rfl

@[simp]
theorem coe_trans (e₁ : A ≃ₐv[R] B) (e₂ : B ≃ₐv[R] C) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

@[simp]
theorem trans_apply (e₁ : A ≃ₐv[R] B) (e₂ : B ≃ₐv[R] C) (x : A) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl

@[simp]
theorem comp_symm (e : A ≃ₐv[R] B) : ValAlgHom.comp (e : A →ₐv[R] B) e.symm = ValAlgHom.id R B := by
  ext
  simp only [ValAlgHom.coe_comp, Function.comp_apply, ValAlgHom.id_apply]
  exact apply_symm_apply e _

@[simp]
theorem symm_comp (e : A ≃ₐv[R] B) : ValAlgHom.comp ↑e.symm (e : A →ₐv[R] B) = ValAlgHom.id R A := by
  ext
  simp only [ValAlgHom.coe_comp, Function.comp_apply, ValAlgHom.id_apply]
  exact symm_apply_apply e _

theorem leftInverse_symm (e : A ≃ₐv[R] B) : Function.LeftInverse e.symm e :=
  e.left_inv

theorem rightInverse_symm (e : A ≃ₐv[R] B) : Function.RightInverse e.symm e :=
  e.right_inv

-- /-- Promotes a bijective valued algebra homomorphism to an algebra equivalence. -/
-- noncomputable def ofBijective (f : A →ₐv[R] B) (hf : Function.Bijective f) : A ≃ₐv[R] B :=
--   { ValRingEquiv.ofBijective (f : A →+*v B) hf, f with }

-- /-- If `A` is equivalent to `A'` and `B` is equivalent to `B'`, then the type of maps
-- `A →ₐv[R] B` is equivalent to the type of maps `A' →ₐv[R] B'`. -/
-- @[simps apply]
-- def arrowCongr (e₁ : A ≃ₐv[R] A') (e₂ : B ≃ₐv[R] B') : (A →ₐv[R] B) ≃ (A' →ₐv[R] B')

-- def equivCongr

instance {R A : Type*} [CommRing R] [Ring A] {ΓR ΓA : outParam Type*} [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [Valued R ΓR] [Valued A ΓA] [ValAlgebra R A] : Group (A ≃ₐv[R] A) where
  mul e e' := e'.trans e
  mul_assoc _ _ _:= rfl
  one := .refl
  one_mul _ := rfl
  mul_one _ := rfl
  inv := symm
  mul_left_inv := symm_trans_self

@[simp]
theorem one_apply (x : A) : (1 : A ≃ₐv[R] A) x = x := rfl

@[simp]
theorem one_def : (1 : A ≃ₐv[R] A) = .refl := rfl

@[simp]
theorem mul_apply (e e' : (A ≃ₐv[R] A)) (x : A) : (e * e') x = e (e' x) := rfl

-- bundled version of forgetful, this will be enhanced to a equiv in certain cases
def toAlgEquivₘ : (A ≃ₐv[R] A) →* (A ≃ₐ[R] A) where
  toFun := ValAlgEquiv.toAlgEquiv (R := R) (A := A) (B := A)
  map_one' := rfl
  map_mul' _ _ := by
    ext
    rfl

@[simp]
theorem toAlgEquivₘ_coe (f : A ≃ₐv[R] A) : toAlgEquivₘ f = (f : A → A) := by
  ext
  rfl

theorem toAlgEquiv_injective : Function.Injective (toAlgEquivₘ : (A ≃ₐv[R] A) →* (A ≃ₐ[R] A)) := by
  intro _ _ h
  apply DFunLike.coe_injective
  exact congrArg ((↑) : (A ≃ₐ[R] A) → A → A) h

end ValAlgEquiv

end ValAlgHom_ValAlgEquiv
