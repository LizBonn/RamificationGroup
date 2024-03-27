import RamificationGroup.Valued.Defs

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
theorem ext (f g : R →+*v S) (h : (f : R → S) = g) : f = g := DFunLike.coe_injective h

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

theorem continuous_of_val_isEquiv_comap {f : R →+* S} (hf : vR.v.IsEquiv (vS.v.comap f)) : Continuous f := sorry -- difficult

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

/-- The identity function as bundled valuation ring homomorphism. -/
def id : R →+*v R :=
  ⟨.id R, continuous_id , IsEquiv.refl⟩

instance : Inhabited (R →+*v R) := ⟨ ValRingHom.id ⟩

@[simp]
theorem id_apply (r : R) : ValRingHom.id r = r := rfl

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
theorem id_comp (f : R →+*v S) : id.comp f = f := by
  ext
  rfl

@[simp]
theorem comp_id (f : R →+*v S) : f.comp id = f := by
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
theorem coe_refl : (refl R : R →+*v R) = .id :=
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
theorem self_trans_symm (e : R ≃+*v S) : e.trans e.symm = .refl R := by
  ext; apply Equiv.left_inv

@[simp]
theorem self_symm_trans (e : R ≃+*v S) : e.symm.trans e = .refl S := by
  ext; apply Equiv.right_inv

-- -- structures on ValRingIso
instance group : Group (R ≃+*v R) where
  mul := .trans
  mul_assoc := by intros; rfl
  one := .refl R
  one_mul := by intros; rfl
  mul_one := by intros; rfl
  inv := .symm
  mul_left_inv := self_symm_trans

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
  __ := ValRingHom.toValAlgebra (ValRingHom.id)

namespace id

@[simp]
theorem map_eq_id : valAlgebraMap R R = ValRingHom.id :=
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

/-- Reinterpret an `ValAlgHom` as a `AlgHom` -/
add_decl_doc ValAlgHom.toAlgHom

/-- Reinterpret an `ValAlgEquiv` as a `ValRingEquiv` -/
add_decl_doc ValAlgEquiv.toValRingEquiv

/-- Reinterpret an `ValAlgEquiv` as a `AlgEquiv` -/
add_decl_doc ValAlgEquiv.toAlgEquiv

@[inherit_doc]
notation:25 A " →ₐv[" R "] " B => ValAlgHom R A B

@[inherit_doc]
notation:25 A " ≃ₐv[" R "] " B => ValAlgEquiv R A B

end Hom

variable {R A B : Type*} [CommRing R] [Ring A] [Ring B] {ΓR ΓA ΓB : outParam Type*} [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [LinearOrderedCommGroupWithZero ΓB] [Valued R ΓR] [vA : Valued A ΓA] [vB : Valued B ΓB] [fA : ValAlgebra R A] [fB : ValAlgebra R B]

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

section

noncomputable def ValAlgHom.mk' (f : A →ₐ[R] B) (h : vA.v.IsEquiv (vB.v.comap f)) : A →ₐv[R] B where
  toFun := f
  map_one' := f.map_one
  map_mul' := f.map_mul
  map_zero' := f.map_zero
  map_add' := f.map_add'
  monotone' := sorry
  val_isEquiv_comap' := h
  commutes' := sorry
  continuous_toFun := sorry

-- `copy lemmas in MonoidWithZeroHom` or `OrderRingHom`
-- `id, symm, comp`

protected def ValAlgHom.id : (A →ₐv[R] A) where
  toOrderRingHom := .id A
  continuous_toFun := continuous_id
  val_isEquiv_comap' := IsEquiv.refl
  commutes' _ := rfl

@[refl]
protected def ValAlgEquiv.refl : (A ≃ₐv[R] A) where
  toOrderRingIso := .refl A
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id
  val_isEquiv_comap' := IsEquiv.refl
  commutes' _ := rfl


instance {R A : Type*} [CommRing R] [Ring A] {ΓR ΓA : outParam Type*} [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [Valued R ΓR] [Valued A ΓA] [ValAlgebra R A] : Group (A ≃ₐv[R] A) where
  mul := sorry
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  inv := sorry
  mul_left_inv := sorry

-- bundled version of forgetful, this will be enhanced to a equiv in certain cases
def ValAlgEquiv.toAlgEquivₘ : (A ≃ₐv[R] A) →* (A ≃ₐ[R] A) where
  toFun := ValAlgEquiv.toAlgEquiv (R := R) (A := A) (B := A)
  map_one' := sorry
  map_mul' := sorry

theorem inj : Function.Injective (ValAlgHom.toAlgHom (R := R) (A := A) (B := A))  := sorry

end

section AlgHom

namespace AlgHomClass

variable {R A B F : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] [FunLike F A B]

-- see Note [lower instance priority]
instance (priority := 100) linearMapClass [AlgHomClass F R A B] : LinearMapClass F R A B :=
  { ‹AlgHomClass F R A B› with
    map_smulₛₗ := fun f r x => by
      simp only [Algebra.smul_def, map_mul, commutes, RingHom.id_apply] }
#align alg_hom_class.linear_map_class AlgHomClass.linearMapClass

-- Porting note: A new definition underlying a coercion `↑`.
/-- Turn an element of a type `F` satisfying `AlgHomClass F α β` into an actual
`AlgHom`. This is declared as the default coercion from `F` to `α →+* β`. -/
@[coe]
def toAlgHom {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : F) : A →ₐ[R] B :=
  { (f : A →+* B) with
      toFun := f
      commutes' := AlgHomClass.commutes f }

instance coeTC {F : Type*} [FunLike F A B] [AlgHomClass F R A B] : CoeTC F (A →ₐ[R] B) :=
  ⟨AlgHomClass.toAlgHom⟩
#align alg_hom_class.alg_hom.has_coe_t AlgHomClass.coeTC

end AlgHomClass

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

section Semiring

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

-- Porting note: we don't port specialized `CoeFun` instances if there is `DFunLike` instead
#noalign alg_hom.has_coe_to_fun

instance funLike : FunLike (A →ₐ[R] B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩
    rcases g with ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩
    congr

-- Porting note: This instance is moved.
instance algHomClass : AlgHomClass (A →ₐ[R] B) R A B where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  commutes f := f.commutes'
#align alg_hom.alg_hom_class AlgHom.algHomClass

/-- See Note [custom simps projection] -/
def Simps.apply {R : Type u} {α : Type v} {β : Type w} [CommSemiring R]
    [Semiring α] [Semiring β] [Algebra R α] [Algebra R β] (f : α →ₐ[R] β) : α → β := f

initialize_simps_projections AlgHom (toFun → apply)

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : F) :
    ⇑(f : A →ₐ[R] B) = f :=
  rfl
#align alg_hom.coe_coe AlgHom.coe_coe

@[simp]
theorem toFun_eq_coe (f : A →ₐ[R] B) : f.toFun = f :=
  rfl
#align alg_hom.to_fun_eq_coe AlgHom.toFun_eq_coe

#noalign alg_hom.coe_ring_hom

-- Porting note: A new definition underlying a coercion `↑`.
@[coe]
def toMonoidHom' (f : A →ₐ[R] B) : A →* B := (f : A →+* B)

instance coeOutMonoidHom : CoeOut (A →ₐ[R] B) (A →* B) :=
  ⟨AlgHom.toMonoidHom'⟩
#align alg_hom.coe_monoid_hom AlgHom.coeOutMonoidHom

-- Porting note: A new definition underlying a coercion `↑`.
@[coe]
def toAddMonoidHom' (f : A →ₐ[R] B) : A →+ B := (f : A →+* B)

instance coeOutAddMonoidHom : CoeOut (A →ₐ[R] B) (A →+ B) :=
  ⟨AlgHom.toAddMonoidHom'⟩
#align alg_hom.coe_add_monoid_hom AlgHom.coeOutAddMonoidHom

-- Porting note: Lean 3: `@[simp, norm_cast] coe_mk`
--               Lean 4: `@[simp] coe_mk` & `@[norm_cast] coe_mks`
@[simp]
theorem coe_mk {f : A →+* B} (h) : ((⟨f, h⟩ : A →ₐ[R] B) : A → B) = f :=
  rfl

@[norm_cast]
theorem coe_mks {f : A → B} (h₁ h₂ h₃ h₄ h₅) : ⇑(⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩ : A →ₐ[R] B) = f :=
  rfl
#align alg_hom.coe_mk AlgHom.coe_mks

-- Porting note: This theorem is new.
@[simp, norm_cast]
theorem coe_ringHom_mk {f : A →+* B} (h) : ((⟨f, h⟩ : A →ₐ[R] B) : A →+* B) = f :=
  rfl

-- make the coercion the simp-normal form
@[simp]
theorem toRingHom_eq_coe (f : A →ₐ[R] B) : f.toRingHom = f :=
  rfl
#align alg_hom.to_ring_hom_eq_coe AlgHom.toRingHom_eq_coe

@[simp, norm_cast]
theorem coe_toRingHom (f : A →ₐ[R] B) : ⇑(f : A →+* B) = f :=
  rfl
#align alg_hom.coe_to_ring_hom AlgHom.coe_toRingHom

@[simp, norm_cast]
theorem coe_toMonoidHom (f : A →ₐ[R] B) : ⇑(f : A →* B) = f :=
  rfl
#align alg_hom.coe_to_monoid_hom AlgHom.coe_toMonoidHom

@[simp, norm_cast]
theorem coe_toAddMonoidHom (f : A →ₐ[R] B) : ⇑(f : A →+ B) = f :=
  rfl
#align alg_hom.coe_to_add_monoid_hom AlgHom.coe_toAddMonoidHom

variable (φ : A →ₐ[R] B)

theorem coe_fn_injective : @Function.Injective (A →ₐ[R] B) (A → B) (↑) :=
  DFunLike.coe_injective
#align alg_hom.coe_fn_injective AlgHom.coe_fn_injective

theorem coe_fn_inj {φ₁ φ₂ : A →ₐ[R] B} : (φ₁ : A → B) = φ₂ ↔ φ₁ = φ₂ :=
  DFunLike.coe_fn_eq
#align alg_hom.coe_fn_inj AlgHom.coe_fn_inj

theorem coe_ringHom_injective : Function.Injective ((↑) : (A →ₐ[R] B) → A →+* B) := fun φ₁ φ₂ H =>
  coe_fn_injective <| show ((φ₁ : A →+* B) : A → B) = ((φ₂ : A →+* B) : A → B) from congr_arg _ H
#align alg_hom.coe_ring_hom_injective AlgHom.coe_ringHom_injective

theorem coe_monoidHom_injective : Function.Injective ((↑) : (A →ₐ[R] B) → A →* B) :=
  RingHom.coe_monoidHom_injective.comp coe_ringHom_injective
#align alg_hom.coe_monoid_hom_injective AlgHom.coe_monoidHom_injective

theorem coe_addMonoidHom_injective : Function.Injective ((↑) : (A →ₐ[R] B) → A →+ B) :=
  RingHom.coe_addMonoidHom_injective.comp coe_ringHom_injective
#align alg_hom.coe_add_monoid_hom_injective AlgHom.coe_addMonoidHom_injective

protected theorem congr_fun {φ₁ φ₂ : A →ₐ[R] B} (H : φ₁ = φ₂) (x : A) : φ₁ x = φ₂ x :=
  DFunLike.congr_fun H x
#align alg_hom.congr_fun AlgHom.congr_fun

protected theorem congr_arg (φ : A →ₐ[R] B) {x y : A} (h : x = y) : φ x = φ y :=
  DFunLike.congr_arg φ h
#align alg_hom.congr_arg AlgHom.congr_arg

@[ext]
theorem ext {φ₁ φ₂ : A →ₐ[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
  DFunLike.ext _ _ H
#align alg_hom.ext AlgHom.ext

theorem ext_iff {φ₁ φ₂ : A →ₐ[R] B} : φ₁ = φ₂ ↔ ∀ x, φ₁ x = φ₂ x :=
  DFunLike.ext_iff
#align alg_hom.ext_iff AlgHom.ext_iff

@[simp]
theorem mk_coe {f : A →ₐ[R] B} (h₁ h₂ h₃ h₄ h₅) : (⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩ : A →ₐ[R] B) = f :=
  ext fun _ => rfl
#align alg_hom.mk_coe AlgHom.mk_coe

@[simp]
theorem commutes (r : R) : φ (algebraMap R A r) = algebraMap R B r :=
  φ.commutes' r
#align alg_hom.commutes AlgHom.commutes

theorem comp_algebraMap : (φ : A →+* B).comp (algebraMap R A) = algebraMap R B :=
  RingHom.ext <| φ.commutes
#align alg_hom.comp_algebra_map AlgHom.comp_algebraMap

protected theorem map_add (r s : A) : φ (r + s) = φ r + φ s :=
  map_add _ _ _
#align alg_hom.map_add AlgHom.map_add

protected theorem map_zero : φ 0 = 0 :=
  map_zero _
#align alg_hom.map_zero AlgHom.map_zero

protected theorem map_mul (x y) : φ (x * y) = φ x * φ y :=
  map_mul _ _ _
#align alg_hom.map_mul AlgHom.map_mul

protected theorem map_one : φ 1 = 1 :=
  map_one _
#align alg_hom.map_one AlgHom.map_one

protected theorem map_pow (x : A) (n : ℕ) : φ (x ^ n) = φ x ^ n :=
  map_pow _ _ _
#align alg_hom.map_pow AlgHom.map_pow

-- @[simp] -- Porting note (#10618): simp can prove this
protected theorem map_smul (r : R) (x : A) : φ (r • x) = r • φ x :=
  map_smul _ _ _
#align alg_hom.map_smul AlgHom.map_smul

protected theorem map_sum {ι : Type*} (f : ι → A) (s : Finset ι) :
    φ (∑ x in s, f x) = ∑ x in s, φ (f x) :=
  map_sum _ _ _
#align alg_hom.map_sum AlgHom.map_sum

protected theorem map_finsupp_sum {α : Type*} [Zero α] {ι : Type*} (f : ι →₀ α) (g : ι → α → A) :
    φ (f.sum g) = f.sum fun i a => φ (g i a) :=
  map_finsupp_sum _ _ _
#align alg_hom.map_finsupp_sum AlgHom.map_finsupp_sum

set_option linter.deprecated false in
protected theorem map_bit0 (x) : φ (bit0 x) = bit0 (φ x) :=
  map_bit0 _ _
#align alg_hom.map_bit0 AlgHom.map_bit0

set_option linter.deprecated false in
protected theorem map_bit1 (x) : φ (bit1 x) = bit1 (φ x) :=
  map_bit1 _ _
#align alg_hom.map_bit1 AlgHom.map_bit1

/-- If a `RingHom` is `R`-linear, then it is an `AlgHom`. -/
def mk' (f : A →+* B) (h : ∀ (c : R) (x), f (c • x) = c • f x) : A →ₐ[R] B :=
  { f with
    toFun := f
    commutes' := fun c => by simp only [Algebra.algebraMap_eq_smul_one, h, f.map_one] }
#align alg_hom.mk' AlgHom.mk'

@[simp]
theorem coe_mk' (f : A →+* B) (h : ∀ (c : R) (x), f (c • x) = c • f x) : ⇑(mk' f h) = f :=
  rfl
#align alg_hom.coe_mk' AlgHom.coe_mk'

section

variable (R A)

/-- Identity map as an `AlgHom`. -/
protected def id : A →ₐ[R] A :=
  { RingHom.id A with commutes' := fun _ => rfl }
#align alg_hom.id AlgHom.id

@[simp]
theorem coe_id : ⇑(AlgHom.id R A) = id :=
  rfl
#align alg_hom.coe_id AlgHom.coe_id

@[simp]
theorem id_toRingHom : (AlgHom.id R A : A →+* A) = RingHom.id _ :=
  rfl
#align alg_hom.id_to_ring_hom AlgHom.id_toRingHom

end

theorem id_apply (p : A) : AlgHom.id R A p = p :=
  rfl
#align alg_hom.id_apply AlgHom.id_apply

/-- Composition of algebra homeomorphisms. -/
def comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : A →ₐ[R] C :=
  { φ₁.toRingHom.comp ↑φ₂ with
    commutes' := fun r : R => by rw [← φ₁.commutes, ← φ₂.commutes]; rfl }
#align alg_hom.comp AlgHom.comp

@[simp]
theorem coe_comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂ :=
  rfl
#align alg_hom.coe_comp AlgHom.coe_comp

theorem comp_apply (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) (p : A) : φ₁.comp φ₂ p = φ₁ (φ₂ p) :=
  rfl
#align alg_hom.comp_apply AlgHom.comp_apply

theorem comp_toRingHom (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) :
    (φ₁.comp φ₂ : A →+* C) = (φ₁ : B →+* C).comp ↑φ₂ :=
  rfl
#align alg_hom.comp_to_ring_hom AlgHom.comp_toRingHom

@[simp]
theorem comp_id : φ.comp (AlgHom.id R A) = φ :=
  ext fun _x => rfl
#align alg_hom.comp_id AlgHom.comp_id

@[simp]
theorem id_comp : (AlgHom.id R B).comp φ = φ :=
  ext fun _x => rfl
#align alg_hom.id_comp AlgHom.id_comp

theorem comp_assoc (φ₁ : C →ₐ[R] D) (φ₂ : B →ₐ[R] C) (φ₃ : A →ₐ[R] B) :
    (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
  ext fun _x => rfl
#align alg_hom.comp_assoc AlgHom.comp_assoc

/-- R-Alg ⥤ R-Mod -/
def toLinearMap : A →ₗ[R] B where
  toFun := φ
  map_add' := map_add _
  map_smul' := map_smul _
#align alg_hom.to_linear_map AlgHom.toLinearMap

@[simp]
theorem toLinearMap_apply (p : A) : φ.toLinearMap p = φ p :=
  rfl
#align alg_hom.to_linear_map_apply AlgHom.toLinearMap_apply

theorem toLinearMap_injective :
    Function.Injective (toLinearMap : _ → A →ₗ[R] B) := fun _φ₁ _φ₂ h =>
  ext <| LinearMap.congr_fun h
#align alg_hom.to_linear_map_injective AlgHom.toLinearMap_injective

@[simp]
theorem comp_toLinearMap (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  rfl
#align alg_hom.comp_to_linear_map AlgHom.comp_toLinearMap

@[simp]
theorem toLinearMap_id : toLinearMap (AlgHom.id R A) = LinearMap.id :=
  LinearMap.ext fun _ => rfl
#align alg_hom.to_linear_map_id AlgHom.toLinearMap_id

/-- Promote a `LinearMap` to an `AlgHom` by supplying proofs about the behavior on `1` and `*`. -/
@[simps]
def ofLinearMap (f : A →ₗ[R] B) (map_one : f 1 = 1) (map_mul : ∀ x y, f (x * y) = f x * f y) :
    A →ₐ[R] B :=
  { f.toAddMonoidHom with
    toFun := f
    map_one' := map_one
    map_mul' := map_mul
    commutes' := fun c => by simp only [Algebra.algebraMap_eq_smul_one, f.map_smul, map_one] }
#align alg_hom.of_linear_map AlgHom.ofLinearMap

@[simp]
theorem ofLinearMap_toLinearMap (map_one) (map_mul) :
    ofLinearMap φ.toLinearMap map_one map_mul = φ := by
  ext
  rfl
#align alg_hom.of_linear_map_to_linear_map AlgHom.ofLinearMap_toLinearMap

@[simp]
theorem toLinearMap_ofLinearMap (f : A →ₗ[R] B) (map_one) (map_mul) :
    toLinearMap (ofLinearMap f map_one map_mul) = f := by
  ext
  rfl
#align alg_hom.to_linear_map_of_linear_map AlgHom.toLinearMap_ofLinearMap

@[simp]
theorem ofLinearMap_id (map_one) (map_mul) :
    ofLinearMap LinearMap.id map_one map_mul = AlgHom.id R A :=
  ext fun _ => rfl
#align alg_hom.of_linear_map_id AlgHom.ofLinearMap_id

theorem map_smul_of_tower {R'} [SMul R' A] [SMul R' B] [LinearMap.CompatibleSMul A B R' R] (r : R')
    (x : A) : φ (r • x) = r • φ x :=
  φ.toLinearMap.map_smul_of_tower r x
#align alg_hom.map_smul_of_tower AlgHom.map_smul_of_tower

theorem map_list_prod (s : List A) : φ s.prod = (s.map φ).prod :=
  φ.toRingHom.map_list_prod s
#align alg_hom.map_list_prod AlgHom.map_list_prod

@[simps (config := .lemmasOnly) toSemigroup_toMul_mul toOne_one]
instance End : Monoid (A →ₐ[R] A) where
  mul := comp
  mul_assoc ϕ ψ χ := rfl
  one := AlgHom.id R A
  one_mul ϕ := ext fun x => rfl
  mul_one ϕ := ext fun x => rfl
#align alg_hom.End AlgHom.End

@[simp]
theorem one_apply (x : A) : (1 : A →ₐ[R] A) x = x :=
  rfl
#align alg_hom.one_apply AlgHom.one_apply

@[simp]
theorem mul_apply (φ ψ : A →ₐ[R] A) (x : A) : (φ * ψ) x = φ (ψ x) :=
  rfl
#align alg_hom.mul_apply AlgHom.mul_apply

theorem algebraMap_eq_apply (f : A →ₐ[R] B) {y : R} {x : A} (h : algebraMap R A y = x) :
    algebraMap R B y = f x :=
  h ▸ (f.commutes _).symm
#align alg_hom.algebra_map_eq_apply AlgHom.algebraMap_eq_apply

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [CommSemiring B]

variable [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)

protected theorem map_multiset_prod (s : Multiset A) : φ s.prod = (s.map φ).prod :=
  map_multiset_prod _ _
#align alg_hom.map_multiset_prod AlgHom.map_multiset_prod

protected theorem map_prod {ι : Type*} (f : ι → A) (s : Finset ι) :
    φ (∏ x in s, f x) = ∏ x in s, φ (f x) :=
  map_prod _ _ _
#align alg_hom.map_prod AlgHom.map_prod

protected theorem map_finsupp_prod {α : Type*} [Zero α] {ι : Type*} (f : ι →₀ α) (g : ι → α → A) :
    φ (f.prod g) = f.prod fun i a => φ (g i a) :=
  map_finsupp_prod _ _ _
#align alg_hom.map_finsupp_prod AlgHom.map_finsupp_prod

end CommSemiring

section Ring

variable [CommSemiring R] [Ring A] [Ring B]

variable [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)

protected theorem map_neg (x) : φ (-x) = -φ x :=
  map_neg _ _
#align alg_hom.map_neg AlgHom.map_neg

protected theorem map_sub (x y) : φ (x - y) = φ x - φ y :=
  map_sub _ _ _
#align alg_hom.map_sub AlgHom.map_sub

end Ring

end AlgHom

namespace RingHom

variable {R S : Type*}

/-- Reinterpret a `RingHom` as an `ℕ`-algebra homomorphism. -/
def toNatAlgHom [Semiring R] [Semiring S] (f : R →+* S) : R →ₐ[ℕ] S :=
  { f with
    toFun := f
    commutes' := fun n => by simp }
#align ring_hom.to_nat_alg_hom RingHom.toNatAlgHom

/-- Reinterpret a `RingHom` as a `ℤ`-algebra homomorphism. -/
def toIntAlgHom [Ring R] [Ring S] [Algebra ℤ R] [Algebra ℤ S] (f : R →+* S) : R →ₐ[ℤ] S :=
  { f with commutes' := fun n => by simp }
#align ring_hom.to_int_alg_hom RingHom.toIntAlgHom

lemma toIntAlgHom_injective [Ring R] [Ring S] [Algebra ℤ R] [Algebra ℤ S] :
    Function.Injective (RingHom.toIntAlgHom : (R →+* S) → _) :=
  fun _ _ e ↦ DFunLike.ext _ _ (fun x ↦ DFunLike.congr_fun e x)

/-- Reinterpret a `RingHom` as a `ℚ`-algebra homomorphism. This actually yields an equivalence,
see `RingHom.equivRatAlgHom`. -/
def toRatAlgHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S) : R →ₐ[ℚ] S :=
  { f with commutes' := f.map_rat_algebraMap }
#align ring_hom.to_rat_alg_hom RingHom.toRatAlgHom

@[simp]
theorem toRatAlgHom_toRingHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S) :
    ↑f.toRatAlgHom = f :=
  RingHom.ext fun _x => rfl
#align ring_hom.to_rat_alg_hom_to_ring_hom RingHom.toRatAlgHom_toRingHom

end RingHom

section

variable {R S : Type*}

@[simp]
theorem AlgHom.toRingHom_toRatAlgHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S]
    (f : R →ₐ[ℚ] S) : (f : R →+* S).toRatAlgHom = f :=
  AlgHom.ext fun _x => rfl
#align alg_hom.to_ring_hom_to_rat_alg_hom AlgHom.toRingHom_toRatAlgHom

/-- The equivalence between `RingHom` and `ℚ`-algebra homomorphisms. -/
@[simps]
def RingHom.equivRatAlgHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] : (R →+* S) ≃ (R →ₐ[ℚ] S)
    where
  toFun := RingHom.toRatAlgHom
  invFun := AlgHom.toRingHom
  left_inv f := RingHom.toRatAlgHom_toRingHom f
  right_inv f := AlgHom.toRingHom_toRatAlgHom f
#align ring_hom.equiv_rat_alg_hom RingHom.equivRatAlgHom

end

namespace Algebra

variable (R : Type u) (A : Type v)

variable [CommSemiring R] [Semiring A] [Algebra R A]

/-- `AlgebraMap` as an `AlgHom`. -/
def ofId : R →ₐ[R] A :=
  { algebraMap R A with commutes' := fun _ => rfl }
#align algebra.of_id Algebra.ofId

variable {R}

theorem ofId_apply (r) : ofId R A r = algebraMap R A r :=
  rfl
#align algebra.of_id_apply Algebra.ofId_apply

/-- This is a special case of a more general instance that we define in a later file. -/
instance subsingleton_id : Subsingleton (R →ₐ[R] A) :=
  ⟨fun f g => AlgHom.ext fun _ => (f.commutes _).trans (g.commutes _).symm⟩

/-- This ext lemma closes trivial subgoals create when chaining heterobasic ext lemmas. -/
@[ext high]
theorem ext_id (f g : R →ₐ[R] A) : f = g := Subsingleton.elim _ _

section MulDistribMulAction

instance : MulDistribMulAction (A →ₐ[R] A) Aˣ where
  smul := fun f => Units.map f
  one_smul := fun x => by ext; rfl
  mul_smul := fun x y z => by ext; rfl
  smul_mul := fun x y z => by ext; exact x.map_mul _ _
  smul_one := fun x => by ext; exact x.map_one

@[simp]
theorem smul_units_def (f : A →ₐ[R] A) (x : Aˣ) :
    f • x = Units.map (f : A →* A) x := rfl

end MulDistribMulAction
end Algebra

namespace MulSemiringAction

variable {M G : Type*} (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

variable [Monoid M] [MulSemiringAction M A] [SMulCommClass M R A]

/-- Each element of the monoid defines an algebra homomorphism.

This is a stronger version of `MulSemiringAction.toRingHom` and
`DistribMulAction.toLinearMap`. -/
@[simps]
def toAlgHom (m : M) : A →ₐ[R] A :=
  { MulSemiringAction.toRingHom _ _ m with
    toFun := fun a => m • a
    commutes' := smul_algebraMap _ }
#align mul_semiring_action.to_alg_hom MulSemiringAction.toAlgHom

theorem toAlgHom_injective [FaithfulSMul M A] :
    Function.Injective (MulSemiringAction.toAlgHom R A : M → A →ₐ[R] A) := fun _m₁ _m₂ h =>
  eq_of_smul_eq_smul fun r => AlgHom.ext_iff.1 h r
#align mul_semiring_action.to_alg_hom_injective MulSemiringAction.toAlgHom_injective

end MulSemiringAction

end AlgHom



/-- An equivalence of algebras is an equivalence of rings commuting with the actions of scalars. -/
structure AlgEquiv (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] extends A ≃ B, A ≃* B, A ≃+ B, A ≃+* B where
  /-- An equivalence of algebras commutes with the action of scalars. -/
  protected commutes' : ∀ r : R, toFun (algebraMap R A r) = algebraMap R B r
#align alg_equiv AlgEquiv

attribute [nolint docBlame] AlgEquiv.toRingEquiv
attribute [nolint docBlame] AlgEquiv.toEquiv
attribute [nolint docBlame] AlgEquiv.toAddEquiv
attribute [nolint docBlame] AlgEquiv.toMulEquiv

@[inherit_doc]
notation:50 A " ≃ₐ[" R "] " A' => AlgEquiv R A A'

/-- `AlgEquivClass F R A B` states that `F` is a type of algebra structure preserving
  equivalences. You should extend this class when you extend `AlgEquiv`. -/
class AlgEquivClass (F : Type*) (R A B : outParam (Type*)) [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] [EquivLike F A B]
    extends RingEquivClass F A B : Prop where
  /-- An equivalence of algebras commutes with the action of scalars. -/
  commutes : ∀ (f : F) (r : R), f (algebraMap R A r) = algebraMap R B r
#align alg_equiv_class AlgEquivClass

-- Porting note: Removed nolint dangerousInstance from AlgEquivClass.toRingEquivClass

namespace AlgEquivClass

-- See note [lower instance priority]
instance (priority := 100) toAlgHomClass (F R A B : Type*) [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] [EquivLike F A B] [h : AlgEquivClass F R A B] :
    AlgHomClass F R A B :=
  { h with }
#align alg_equiv_class.to_alg_hom_class AlgEquivClass.toAlgHomClass

instance (priority := 100) toLinearEquivClass (F R A B : Type*) [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [EquivLike F A B] [h : AlgEquivClass F R A B] : LinearEquivClass F R A B :=
  { h with map_smulₛₗ := fun f => map_smulₛₗ f }
#align alg_equiv_class.to_linear_equiv_class AlgEquivClass.toLinearEquivClass

/-- Turn an element of a type `F` satisfying `AlgEquivClass F R A B` into an actual `AlgEquiv`.
This is declared as the default coercion from `F` to `A ≃ₐ[R] B`. -/
@[coe]
def toAlgEquiv {F R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
    [Algebra R B] [EquivLike F A B] [AlgEquivClass F R A B] (f : F) : A ≃ₐ[R] B :=
  { (f : A ≃ B), (f : A ≃+* B) with commutes' := commutes f }

instance (F R A B : Type*) [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [EquivLike F A B] [AlgEquivClass F R A B] : CoeTC F (A ≃ₐ[R] B) :=
  ⟨toAlgEquiv⟩
end AlgEquivClass

namespace AlgEquiv

universe uR uA₁ uA₂ uA₃ uA₁' uA₂' uA₃'
variable {R : Type uR}
variable {A₁ : Type uA₁} {A₂ : Type uA₂} {A₃ : Type uA₃}
variable {A₁' : Type uA₁'} {A₂' : Type uA₂'} {A₃' : Type uA₃'}

section Semiring

variable [CommSemiring R] [Semiring A₁] [Semiring A₂] [Semiring A₃]
variable [Semiring A₁'] [Semiring A₂'] [Semiring A₃']

variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]
variable [Algebra R A₁'] [Algebra R A₂'] [Algebra R A₃']

variable (e : A₁ ≃ₐ[R] A₂)

instance : EquivLike (A₁ ≃ₐ[R] A₂) A₁ A₂ where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨f,_⟩,_⟩ := f
    obtain ⟨⟨g,_⟩,_⟩ := g
    congr

/-- Helper instance since the coercion is not always found. -/
instance : FunLike (A₁ ≃ₐ[R] A₂) A₁ A₂ where
  coe := DFunLike.coe
  coe_injective' := DFunLike.coe_injective'

instance : AlgEquivClass (A₁ ≃ₐ[R] A₂) R A₁ A₂ where
  map_add f := f.map_add'
  map_mul f := f.map_mul'
  commutes f := f.commutes'

-- Porting note: the default simps projection was `e.toEquiv.toFun`, it should be `FunLike.coe`
/-- See Note [custom simps projection] -/
def Simps.apply (e : A₁ ≃ₐ[R] A₂) : A₁ → A₂ :=
  e

-- Porting note: the default simps projection was `e.toEquiv`, it should be `EquivLike.toEquiv`
/-- See Note [custom simps projection] -/
def Simps.toEquiv (e : A₁ ≃ₐ[R] A₂) : A₁ ≃ A₂ :=
  e

-- Porting note: `protected` used to be an attribute below
@[simp]
protected theorem coe_coe {F : Type*} [EquivLike F A₁ A₂] [AlgEquivClass F R A₁ A₂] (f : F) :
    ⇑(f : A₁ ≃ₐ[R] A₂) = f :=
  rfl
#align alg_equiv.coe_coe AlgEquiv.coe_coe

@[ext]
theorem ext {f g : A₁ ≃ₐ[R] A₂} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h
#align alg_equiv.ext AlgEquiv.ext

protected theorem congr_arg {f : A₁ ≃ₐ[R] A₂} {x x' : A₁} : x = x' → f x = f x' :=
  DFunLike.congr_arg f
#align alg_equiv.congr_arg AlgEquiv.congr_arg

protected theorem congr_fun {f g : A₁ ≃ₐ[R] A₂} (h : f = g) (x : A₁) : f x = g x :=
  DFunLike.congr_fun h x
#align alg_equiv.congr_fun AlgEquiv.congr_fun

protected theorem ext_iff {f g : A₁ ≃ₐ[R] A₂} : f = g ↔ ∀ x, f x = g x :=
  DFunLike.ext_iff
#align alg_equiv.ext_iff AlgEquiv.ext_iff

theorem coe_fun_injective : @Function.Injective (A₁ ≃ₐ[R] A₂) (A₁ → A₂) fun e => (e : A₁ → A₂) :=
  DFunLike.coe_injective
#align alg_equiv.coe_fun_injective AlgEquiv.coe_fun_injective

-- Porting note: Made to CoeOut instance from Coe, not dangerous anymore
instance hasCoeToRingEquiv : CoeOut (A₁ ≃ₐ[R] A₂) (A₁ ≃+* A₂) :=
  ⟨AlgEquiv.toRingEquiv⟩
#align alg_equiv.has_coe_to_ring_equiv AlgEquiv.hasCoeToRingEquiv

@[simp]
theorem coe_mk {toFun invFun left_inv right_inv map_mul map_add commutes} :
    ⇑(⟨⟨toFun, invFun, left_inv, right_inv⟩, map_mul, map_add, commutes⟩ : A₁ ≃ₐ[R] A₂) = toFun :=
  rfl
#align alg_equiv.coe_mk AlgEquiv.coe_mk

@[simp]
theorem mk_coe (e : A₁ ≃ₐ[R] A₂) (e' h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨e, e', h₁, h₂⟩, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂) = e :=
  ext fun _ => rfl
#align alg_equiv.mk_coe AlgEquiv.mk_coe

-- Porting note: `toFun_eq_coe` no longer needed in Lean4
#noalign alg_equiv.to_fun_eq_coe

@[simp]
theorem toEquiv_eq_coe : e.toEquiv = e :=
  rfl
#align alg_equiv.to_equiv_eq_coe AlgEquiv.toEquiv_eq_coe

@[simp]
theorem toRingEquiv_eq_coe : e.toRingEquiv = e :=
  rfl
#align alg_equiv.to_ring_equiv_eq_coe AlgEquiv.toRingEquiv_eq_coe

@[simp, norm_cast]
lemma toRingEquiv_toRingHom : ((e : A₁ ≃+* A₂) : A₁ →+* A₂) = e :=
  rfl

@[simp, norm_cast]
theorem coe_ringEquiv : ((e : A₁ ≃+* A₂) : A₁ → A₂) = e :=
  rfl
#align alg_equiv.coe_ring_equiv AlgEquiv.coe_ringEquiv

theorem coe_ringEquiv' : (e.toRingEquiv : A₁ → A₂) = e :=
  rfl
#align alg_equiv.coe_ring_equiv' AlgEquiv.coe_ringEquiv'

theorem coe_ringEquiv_injective : Function.Injective ((↑) : (A₁ ≃ₐ[R] A₂) → A₁ ≃+* A₂) :=
  fun _ _ h => ext <| RingEquiv.congr_fun h
#align alg_equiv.coe_ring_equiv_injective AlgEquiv.coe_ringEquiv_injective

protected theorem map_add : ∀ x y, e (x + y) = e x + e y :=
  map_add e
#align alg_equiv.map_add AlgEquiv.map_add

protected theorem map_zero : e 0 = 0 :=
  map_zero e
#align alg_equiv.map_zero AlgEquiv.map_zero

protected theorem map_mul : ∀ x y, e (x * y) = e x * e y :=
  map_mul e
#align alg_equiv.map_mul AlgEquiv.map_mul

protected theorem map_one : e 1 = 1 :=
  map_one e
#align alg_equiv.map_one AlgEquiv.map_one

@[simp]
theorem commutes : ∀ r : R, e (algebraMap R A₁ r) = algebraMap R A₂ r :=
  e.commutes'
#align alg_equiv.commutes AlgEquiv.commutes

-- @[simp] -- Porting note (#10618): simp can prove this
theorem map_smul (r : R) (x : A₁) : e (r • x) = r • e x := by
  simp only [Algebra.smul_def, map_mul, commutes]
#align alg_equiv.map_smul AlgEquiv.map_smul

@[deprecated map_sum]
nonrec theorem map_sum {ι : Type*} (f : ι → A₁) (s : Finset ι) :
    e (∑ x in s, f x) = ∑ x in s, e (f x) :=
  map_sum e f s
#align alg_equiv.map_sum AlgEquiv.map_sum

theorem map_finsupp_sum {α : Type*} [Zero α] {ι : Type*} (f : ι →₀ α) (g : ι → α → A₁) :
    e (f.sum g) = f.sum fun i b => e (g i b) :=
  e.map_sum _ _
#align alg_equiv.map_finsupp_sum AlgEquiv.map_finsupp_sum

-- Porting note: Added [coe] attribute
/-- Interpret an algebra equivalence as an algebra homomorphism.

This definition is included for symmetry with the other `to*Hom` projections.
The `simp` normal form is to use the coercion of the `AlgHomClass.coeTC` instance. -/
@[coe]
def toAlgHom : A₁ →ₐ[R] A₂ :=
  { e with
    map_one' := e.map_one
    map_zero' := e.map_zero }
#align alg_equiv.to_alg_hom AlgEquiv.toAlgHom

@[simp]
theorem toAlgHom_eq_coe : e.toAlgHom = e :=
  rfl
#align alg_equiv.to_alg_hom_eq_coe AlgEquiv.toAlgHom_eq_coe

@[simp, norm_cast]
theorem coe_algHom : DFunLike.coe (e.toAlgHom) = DFunLike.coe e :=
  rfl
#align alg_equiv.coe_alg_hom AlgEquiv.coe_algHom

theorem coe_algHom_injective : Function.Injective ((↑) : (A₁ ≃ₐ[R] A₂) → A₁ →ₐ[R] A₂) :=
  fun _ _ h => ext <| AlgHom.congr_fun h
#align alg_equiv.coe_alg_hom_injective AlgEquiv.coe_algHom_injective

@[simp, norm_cast]
lemma toAlgHom_toRingHom : ((e : A₁ →ₐ[R] A₂) : A₁ →+* A₂) = e :=
  rfl

/-- The two paths coercion can take to a `RingHom` are equivalent -/
theorem coe_ringHom_commutes : ((e : A₁ →ₐ[R] A₂) : A₁ →+* A₂) = ((e : A₁ ≃+* A₂) : A₁ →+* A₂) :=
  rfl
#align alg_equiv.coe_ring_hom_commutes AlgEquiv.coe_ringHom_commutes

protected theorem map_pow : ∀ (x : A₁) (n : ℕ), e (x ^ n) = e x ^ n :=
  map_pow _
#align alg_equiv.map_pow AlgEquiv.map_pow

protected theorem injective : Function.Injective e :=
  EquivLike.injective e
#align alg_equiv.injective AlgEquiv.injective

protected theorem surjective : Function.Surjective e :=
  EquivLike.surjective e
#align alg_equiv.surjective AlgEquiv.surjective

protected theorem bijective : Function.Bijective e :=
  EquivLike.bijective e
#align alg_equiv.bijective AlgEquiv.bijective

/-- Algebra equivalences are reflexive. -/
@[refl]
def refl : A₁ ≃ₐ[R] A₁ :=
  { (1 : A₁ ≃+* A₁) with commutes' := fun _ => rfl }
#align alg_equiv.refl AlgEquiv.refl

instance : Inhabited (A₁ ≃ₐ[R] A₁) :=
  ⟨refl⟩

@[simp]
theorem refl_toAlgHom : ↑(refl : A₁ ≃ₐ[R] A₁) = AlgHom.id R A₁ :=
  rfl
#align alg_equiv.refl_to_alg_hom AlgEquiv.refl_toAlgHom

@[simp]
theorem coe_refl : ⇑(refl : A₁ ≃ₐ[R] A₁) = id :=
  rfl
#align alg_equiv.coe_refl AlgEquiv.coe_refl

/-- Algebra equivalences are symmetric. -/
@[symm]
def symm (e : A₁ ≃ₐ[R] A₂) : A₂ ≃ₐ[R] A₁ :=
  { e.toRingEquiv.symm with
    commutes' := fun r => by
      rw [← e.toRingEquiv.symm_apply_apply (algebraMap R A₁ r)]
      congr
      change _ = e _
      rw [e.commutes] }
#align alg_equiv.symm AlgEquiv.symm

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : A₁ ≃ₐ[R] A₂) : A₂ → A₁ :=
  e.symm
#align alg_equiv.simps.symm_apply AlgEquiv.Simps.symm_apply

initialize_simps_projections AlgEquiv (toFun → apply, invFun → symm_apply)

--@[simp] -- Porting note (#10618): simp can prove this once symm_mk is introduced
theorem coe_apply_coe_coe_symm_apply {F : Type*} [EquivLike F A₁ A₂] [AlgEquivClass F R A₁ A₂]
    (f : F) (x : A₂) :
    f ((f : A₁ ≃ₐ[R] A₂).symm x) = x :=
  EquivLike.right_inv f x
#align alg_equiv.coe_apply_coe_coe_symm_apply AlgEquiv.coe_apply_coe_coe_symm_apply

--@[simp] -- Porting note (#10618): simp can prove this once symm_mk is introduced
theorem coe_coe_symm_apply_coe_apply {F : Type*} [EquivLike F A₁ A₂] [AlgEquivClass F R A₁ A₂]
    (f : F) (x : A₁) :
    (f : A₁ ≃ₐ[R] A₂).symm (f x) = x :=
  EquivLike.left_inv f x
#align alg_equiv.coe_coe_symm_apply_coe_apply AlgEquiv.coe_coe_symm_apply_coe_apply

-- Porting note: `simp` normal form of `invFun_eq_symm`
@[simp]
theorem symm_toEquiv_eq_symm {e : A₁ ≃ₐ[R] A₂} : (e : A₁ ≃ A₂).symm = e.symm :=
  rfl

theorem invFun_eq_symm {e : A₁ ≃ₐ[R] A₂} : e.invFun = e.symm :=
  rfl
#align alg_equiv.inv_fun_eq_symm AlgEquiv.invFun_eq_symm

@[simp]
theorem symm_symm (e : A₁ ≃ₐ[R] A₂) : e.symm.symm = e := by
  ext
  rfl
#align alg_equiv.symm_symm AlgEquiv.symm_symm

theorem symm_bijective : Function.Bijective (symm : (A₁ ≃ₐ[R] A₂) → A₂ ≃ₐ[R] A₁) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩
#align alg_equiv.symm_bijective AlgEquiv.symm_bijective

@[simp]
theorem mk_coe' (e : A₁ ≃ₐ[R] A₂) (f h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨f, e, h₁, h₂⟩, h₃, h₄, h₅⟩ : A₂ ≃ₐ[R] A₁) = e.symm :=
  symm_bijective.injective <| ext fun _ => rfl
#align alg_equiv.mk_coe' AlgEquiv.mk_coe'

@[simp]
theorem symm_mk (f f') (h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨f, f', h₁, h₂⟩, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂).symm =
      {(⟨⟨f, f', h₁, h₂⟩, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂).symm with
        toFun := f'
        invFun := f } :=
  rfl
#align alg_equiv.symm_mk AlgEquiv.symm_mk

@[simp]
theorem refl_symm : (AlgEquiv.refl : A₁ ≃ₐ[R] A₁).symm = AlgEquiv.refl :=
  rfl
#align alg_equiv.refl_symm AlgEquiv.refl_symm

--this should be a simp lemma but causes a lint timeout
theorem toRingEquiv_symm (f : A₁ ≃ₐ[R] A₁) : (f : A₁ ≃+* A₁).symm = f.symm :=
  rfl
#align alg_equiv.to_ring_equiv_symm AlgEquiv.toRingEquiv_symm

@[simp]
theorem symm_toRingEquiv : (e.symm : A₂ ≃+* A₁) = (e : A₁ ≃+* A₂).symm :=
  rfl
#align alg_equiv.symm_to_ring_equiv AlgEquiv.symm_toRingEquiv

/-- Algebra equivalences are transitive. -/
@[trans]
def trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : A₁ ≃ₐ[R] A₃ :=
  { e₁.toRingEquiv.trans e₂.toRingEquiv with
    commutes' := fun r => show e₂.toFun (e₁.toFun _) = _ by rw [e₁.commutes', e₂.commutes'] }
#align alg_equiv.trans AlgEquiv.trans

@[simp]
theorem apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : ∀ x, e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply
#align alg_equiv.apply_symm_apply AlgEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : ∀ x, e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply
#align alg_equiv.symm_apply_apply AlgEquiv.symm_apply_apply

@[simp]
theorem symm_trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₃) :
    (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
  rfl
#align alg_equiv.symm_trans_apply AlgEquiv.symm_trans_apply

@[simp]
theorem coe_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl
#align alg_equiv.coe_trans AlgEquiv.coe_trans

@[simp]
theorem trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₁) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl
#align alg_equiv.trans_apply AlgEquiv.trans_apply

@[simp]
theorem comp_symm (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp (e : A₁ →ₐ[R] A₂) ↑e.symm = AlgHom.id R A₂ := by
  ext
  simp
#align alg_equiv.comp_symm AlgEquiv.comp_symm

@[simp]
theorem symm_comp (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp ↑e.symm (e : A₁ →ₐ[R] A₂) = AlgHom.id R A₁ := by
  ext
  simp
#align alg_equiv.symm_comp AlgEquiv.symm_comp

theorem leftInverse_symm (e : A₁ ≃ₐ[R] A₂) : Function.LeftInverse e.symm e :=
  e.left_inv
#align alg_equiv.left_inverse_symm AlgEquiv.leftInverse_symm

theorem rightInverse_symm (e : A₁ ≃ₐ[R] A₂) : Function.RightInverse e.symm e :=
  e.right_inv
#align alg_equiv.right_inverse_symm AlgEquiv.rightInverse_symm

/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'`, then the type of maps
`A₁ →ₐ[R] A₂` is equivalent to the type of maps `A₁' →ₐ[R] A₂'`. -/
@[simps apply]
def arrowCongr (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') : (A₁ →ₐ[R] A₂) ≃ (A₁' →ₐ[R] A₂') where
  toFun f := (e₂.toAlgHom.comp f).comp e₁.symm.toAlgHom
  invFun f := (e₂.symm.toAlgHom.comp f).comp e₁.toAlgHom
  left_inv f := by
    simp only [AlgHom.comp_assoc, toAlgHom_eq_coe, symm_comp]
    simp only [← AlgHom.comp_assoc, symm_comp, AlgHom.id_comp, AlgHom.comp_id]
  right_inv f := by
    simp only [AlgHom.comp_assoc, toAlgHom_eq_coe, comp_symm]
    simp only [← AlgHom.comp_assoc, comp_symm, AlgHom.id_comp, AlgHom.comp_id]
#align alg_equiv.arrow_congr AlgEquiv.arrowCongr

theorem arrowCongr_comp (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂')
    (e₃ : A₃ ≃ₐ[R] A₃') (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₃) :
    arrowCongr e₁ e₃ (g.comp f) = (arrowCongr e₂ e₃ g).comp (arrowCongr e₁ e₂ f) := by
  ext
  simp only [arrowCongr, Equiv.coe_fn_mk, AlgHom.comp_apply]
  congr
  exact (e₂.symm_apply_apply _).symm
#align alg_equiv.arrow_congr_comp AlgEquiv.arrowCongr_comp

@[simp]
theorem arrowCongr_refl : arrowCongr AlgEquiv.refl AlgEquiv.refl = Equiv.refl (A₁ →ₐ[R] A₂) := by
  ext
  rfl
#align alg_equiv.arrow_congr_refl AlgEquiv.arrowCongr_refl

@[simp]
theorem arrowCongr_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₁' : A₁' ≃ₐ[R] A₂')
    (e₂ : A₂ ≃ₐ[R] A₃) (e₂' : A₂' ≃ₐ[R] A₃') :
    arrowCongr (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂') := by
  ext
  rfl
#align alg_equiv.arrow_congr_trans AlgEquiv.arrowCongr_trans

@[simp]
theorem arrowCongr_symm (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') :
    (arrowCongr e₁ e₂).symm = arrowCongr e₁.symm e₂.symm := by
  ext
  rfl
#align alg_equiv.arrow_congr_symm AlgEquiv.arrowCongr_symm

/-- If `A₁` is equivalent to `A₂` and `A₁'` is equivalent to `A₂'`, then the type of maps
`A₁ ≃ₐ[R] A₁'` is equivalent to the type of maps `A₂ ≃ ₐ[R] A₂'`.

This is the `AlgEquiv` version of `AlgEquiv.arrowCongr`. -/
@[simps apply]
def equivCongr (e : A₁ ≃ₐ[R] A₂) (e' : A₁' ≃ₐ[R] A₂') : (A₁ ≃ₐ[R] A₁') ≃ A₂ ≃ₐ[R] A₂' where
  toFun ψ := e.symm.trans (ψ.trans e')
  invFun ψ := e.trans (ψ.trans e'.symm)
  left_inv ψ := by
    ext
    simp_rw [trans_apply, symm_apply_apply]
  right_inv ψ := by
    ext
    simp_rw [trans_apply, apply_symm_apply]

@[simp]
theorem equivCongr_refl : equivCongr AlgEquiv.refl AlgEquiv.refl = Equiv.refl (A₁ ≃ₐ[R] A₁') := by
  ext
  rfl

@[simp]
theorem equivCongr_symm (e : A₁ ≃ₐ[R] A₂) (e' : A₁' ≃ₐ[R] A₂') :
    (equivCongr e e').symm = equivCongr e.symm e'.symm :=
  rfl

@[simp]
theorem equivCongr_trans (e₁₂ : A₁ ≃ₐ[R] A₂) (e₁₂' : A₁' ≃ₐ[R] A₂')
    (e₂₃ : A₂ ≃ₐ[R] A₃) (e₂₃' : A₂' ≃ₐ[R] A₃') :
    (equivCongr e₁₂ e₁₂').trans (equivCongr e₂₃ e₂₃') =
      equivCongr (e₁₂.trans e₂₃) (e₁₂'.trans e₂₃') :=
  rfl

/-- If an algebra morphism has an inverse, it is an algebra isomorphism. -/
def ofAlgHom (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ : f.comp g = AlgHom.id R A₂)
    (h₂ : g.comp f = AlgHom.id R A₁) : A₁ ≃ₐ[R] A₂ :=
  { f with
    toFun := f
    invFun := g
    left_inv := AlgHom.ext_iff.1 h₂
    right_inv := AlgHom.ext_iff.1 h₁ }
#align alg_equiv.of_alg_hom AlgEquiv.ofAlgHom

theorem coe_algHom_ofAlgHom (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
    ↑(ofAlgHom f g h₁ h₂) = f :=
  AlgHom.ext fun _ => rfl
#align alg_equiv.coe_alg_hom_of_alg_hom AlgEquiv.coe_algHom_ofAlgHom

@[simp]
theorem ofAlgHom_coe_algHom (f : A₁ ≃ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
    ofAlgHom (↑f) g h₁ h₂ = f :=
  ext fun _ => rfl
#align alg_equiv.of_alg_hom_coe_alg_hom AlgEquiv.ofAlgHom_coe_algHom

theorem ofAlgHom_symm (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
    (ofAlgHom f g h₁ h₂).symm = ofAlgHom g f h₂ h₁ :=
  rfl
#align alg_equiv.of_alg_hom_symm AlgEquiv.ofAlgHom_symm

/-- Promotes a bijective algebra homomorphism to an algebra equivalence. -/
noncomputable def ofBijective (f : A₁ →ₐ[R] A₂) (hf : Function.Bijective f) : A₁ ≃ₐ[R] A₂ :=
  { RingEquiv.ofBijective (f : A₁ →+* A₂) hf, f with }
#align alg_equiv.of_bijective AlgEquiv.ofBijective

@[simp]
theorem coe_ofBijective {f : A₁ →ₐ[R] A₂} {hf : Function.Bijective f} :
    (AlgEquiv.ofBijective f hf : A₁ → A₂) = f :=
  rfl
#align alg_equiv.coe_of_bijective AlgEquiv.coe_ofBijective

theorem ofBijective_apply {f : A₁ →ₐ[R] A₂} {hf : Function.Bijective f} (a : A₁) :
    (AlgEquiv.ofBijective f hf) a = f a :=
  rfl
#align alg_equiv.of_bijective_apply AlgEquiv.ofBijective_apply

/-- Forgetting the multiplicative structures, an equivalence of algebras is a linear equivalence. -/
@[simps apply]
def toLinearEquiv (e : A₁ ≃ₐ[R] A₂) : A₁ ≃ₗ[R] A₂ :=
  { e with
    toFun := e
    map_smul' := e.map_smul
    invFun := e.symm }
#align alg_equiv.to_linear_equiv AlgEquiv.toLinearEquiv
#align alg_equiv.to_linear_equiv_apply AlgEquiv.toLinearEquiv_apply

@[simp]
theorem toLinearEquiv_refl : (AlgEquiv.refl : A₁ ≃ₐ[R] A₁).toLinearEquiv = LinearEquiv.refl R A₁ :=
  rfl
#align alg_equiv.to_linear_equiv_refl AlgEquiv.toLinearEquiv_refl

@[simp]
theorem toLinearEquiv_symm (e : A₁ ≃ₐ[R] A₂) : e.toLinearEquiv.symm = e.symm.toLinearEquiv :=
  rfl
#align alg_equiv.to_linear_equiv_symm AlgEquiv.toLinearEquiv_symm

@[simp]
theorem toLinearEquiv_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) :
    (e₁.trans e₂).toLinearEquiv = e₁.toLinearEquiv.trans e₂.toLinearEquiv :=
  rfl
#align alg_equiv.to_linear_equiv_trans AlgEquiv.toLinearEquiv_trans

theorem toLinearEquiv_injective : Function.Injective (toLinearEquiv : _ → A₁ ≃ₗ[R] A₂) :=
  fun _ _ h => ext <| LinearEquiv.congr_fun h
#align alg_equiv.to_linear_equiv_injective AlgEquiv.toLinearEquiv_injective

/-- Interpret an algebra equivalence as a linear map. -/
def toLinearMap : A₁ →ₗ[R] A₂ :=
  e.toAlgHom.toLinearMap
#align alg_equiv.to_linear_map AlgEquiv.toLinearMap

@[simp]
theorem toAlgHom_toLinearMap : (e : A₁ →ₐ[R] A₂).toLinearMap = e.toLinearMap :=
  rfl
#align alg_equiv.to_alg_hom_to_linear_map AlgEquiv.toAlgHom_toLinearMap

theorem toLinearMap_ofAlgHom (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
    (ofAlgHom f g h₁ h₂).toLinearMap = f.toLinearMap :=
  LinearMap.ext fun _ => rfl

@[simp]
theorem toLinearEquiv_toLinearMap : e.toLinearEquiv.toLinearMap = e.toLinearMap :=
  rfl
#align alg_equiv.to_linear_equiv_to_linear_map AlgEquiv.toLinearEquiv_toLinearMap

@[simp]
theorem toLinearMap_apply (x : A₁) : e.toLinearMap x = e x :=
  rfl
#align alg_equiv.to_linear_map_apply AlgEquiv.toLinearMap_apply

theorem toLinearMap_injective : Function.Injective (toLinearMap : _ → A₁ →ₗ[R] A₂) := fun _ _ h =>
  ext <| LinearMap.congr_fun h
#align alg_equiv.to_linear_map_injective AlgEquiv.toLinearMap_injective

@[simp]
theorem trans_toLinearMap (f : A₁ ≃ₐ[R] A₂) (g : A₂ ≃ₐ[R] A₃) :
    (f.trans g).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  rfl
#align alg_equiv.trans_to_linear_map AlgEquiv.trans_toLinearMap

section OfLinearEquiv

variable (l : A₁ ≃ₗ[R] A₂) (map_one : l 1 = 1) (map_mul : ∀ x y : A₁, l (x * y) = l x * l y)

/-- Upgrade a linear equivalence to an algebra equivalence,
given that it distributes over multiplication and the identity
-/
@[simps apply]
def ofLinearEquiv : A₁ ≃ₐ[R] A₂ :=
  { l with
    toFun := l
    invFun := l.symm
    map_mul' := map_mul
    commutes' := (AlgHom.ofLinearMap l map_one map_mul : A₁ →ₐ[R] A₂).commutes }
#align alg_equiv.of_linear_equiv AlgEquiv.ofLinearEquivₓ

@[simp]
theorem ofLinearEquiv_symm :
    (ofLinearEquiv l map_one map_mul).symm =
      ofLinearEquiv l.symm (ofLinearEquiv l map_one map_mul).symm.map_one
        (ofLinearEquiv l map_one map_mul).symm.map_mul :=
  rfl
#align alg_equiv.of_linear_equiv_symm AlgEquiv.ofLinearEquiv_symm

@[simp]
theorem ofLinearEquiv_toLinearEquiv (map_mul) (map_one) :
    ofLinearEquiv e.toLinearEquiv map_mul map_one = e := by
  ext
  rfl
#align alg_equiv.of_linear_equiv_to_linear_equiv AlgEquiv.ofLinearEquiv_toLinearEquiv

@[simp]
theorem toLinearEquiv_ofLinearEquiv : toLinearEquiv (ofLinearEquiv l map_one map_mul) = l := by
  ext
  rfl
#align alg_equiv.to_linear_equiv_of_linear_equiv AlgEquiv.toLinearEquiv_ofLinearEquiv

end OfLinearEquiv

section OfRingEquiv

/-- Promotes a linear ring_equiv to an AlgEquiv. -/
@[simps apply symm_apply toEquiv] -- Porting note: don't want redundant `toEquiv_symm_apply` simps
def ofRingEquiv {f : A₁ ≃+* A₂} (hf : ∀ x, f (algebraMap R A₁ x) = algebraMap R A₂ x) :
    A₁ ≃ₐ[R] A₂ :=
  { f with
    toFun := f
    invFun := f.symm
    commutes' := hf }
#align alg_equiv.of_ring_equiv AlgEquiv.ofRingEquiv

end OfRingEquiv

-- Porting note: projections mul & one not found, removed [simps] and added theorems manually
-- @[simps (config := .lemmasOnly) one]
instance aut : Group (A₁ ≃ₐ[R] A₁) where
  mul ϕ ψ := ψ.trans ϕ
  mul_assoc ϕ ψ χ := rfl
  one := refl
  one_mul ϕ := ext fun x => rfl
  mul_one ϕ := ext fun x => rfl
  inv := symm
  mul_left_inv ϕ := ext <| symm_apply_apply ϕ
#align alg_equiv.aut AlgEquiv.aut

theorem aut_mul (ϕ ψ : A₁ ≃ₐ[R] A₁) : ϕ * ψ = ψ.trans ϕ :=
  rfl

theorem aut_one : 1 = AlgEquiv.refl (R := R) (A₁ := A₁) :=
  rfl

@[simp]
theorem one_apply (x : A₁) : (1 : A₁ ≃ₐ[R] A₁) x = x :=
  rfl
#align alg_equiv.one_apply AlgEquiv.one_apply

@[simp]
theorem mul_apply (e₁ e₂ : A₁ ≃ₐ[R] A₁) (x : A₁) : (e₁ * e₂) x = e₁ (e₂ x) :=
  rfl
#align alg_equiv.mul_apply AlgEquiv.mul_apply

/-- An algebra isomorphism induces a group isomorphism between automorphism groups.

This is a more bundled version of `AlgEquiv.equivCongr`. -/
@[simps apply]
def autCongr (ϕ : A₁ ≃ₐ[R] A₂) : (A₁ ≃ₐ[R] A₁) ≃* A₂ ≃ₐ[R] A₂ where
  __ := equivCongr ϕ ϕ
  toFun ψ := ϕ.symm.trans (ψ.trans ϕ)
  invFun ψ := ϕ.trans (ψ.trans ϕ.symm)
  map_mul' ψ χ := by
    ext
    simp only [mul_apply, trans_apply, symm_apply_apply]
#align alg_equiv.aut_congr AlgEquiv.autCongr

@[simp]
theorem autCongr_refl : autCongr AlgEquiv.refl = MulEquiv.refl (A₁ ≃ₐ[R] A₁) := by
  ext
  rfl
#align alg_equiv.aut_congr_refl AlgEquiv.autCongr_refl

@[simp]
theorem autCongr_symm (ϕ : A₁ ≃ₐ[R] A₂) : (autCongr ϕ).symm = autCongr ϕ.symm :=
  rfl
#align alg_equiv.aut_congr_symm AlgEquiv.autCongr_symm

@[simp]
theorem autCongr_trans (ϕ : A₁ ≃ₐ[R] A₂) (ψ : A₂ ≃ₐ[R] A₃) :
    (autCongr ϕ).trans (autCongr ψ) = autCongr (ϕ.trans ψ) :=
  rfl
#align alg_equiv.aut_congr_trans AlgEquiv.autCongr_trans

/-- The tautological action by `A₁ ≃ₐ[R] A₁` on `A₁`.

This generalizes `Function.End.applyMulAction`. -/
instance applyMulSemiringAction : MulSemiringAction (A₁ ≃ₐ[R] A₁) A₁ where
  smul := (· <| ·)
  smul_zero := AlgEquiv.map_zero
  smul_add := AlgEquiv.map_add
  smul_one := AlgEquiv.map_one
  smul_mul := AlgEquiv.map_mul
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
#align alg_equiv.apply_mul_semiring_action AlgEquiv.applyMulSemiringAction

@[simp]
protected theorem smul_def (f : A₁ ≃ₐ[R] A₁) (a : A₁) : f • a = f a :=
  rfl
#align alg_equiv.smul_def AlgEquiv.smul_def

instance apply_faithfulSMul : FaithfulSMul (A₁ ≃ₐ[R] A₁) A₁ :=
  ⟨AlgEquiv.ext⟩
#align alg_equiv.apply_has_faithful_smul AlgEquiv.apply_faithfulSMul

instance apply_smulCommClass : SMulCommClass R (A₁ ≃ₐ[R] A₁) A₁ where
  smul_comm r e a := (e.map_smul r a).symm
#align alg_equiv.apply_smul_comm_class AlgEquiv.apply_smulCommClass

instance apply_smulCommClass' : SMulCommClass (A₁ ≃ₐ[R] A₁) R A₁ where
  smul_comm e r a := e.map_smul r a
#align alg_equiv.apply_smul_comm_class' AlgEquiv.apply_smulCommClass'

instance : MulDistribMulAction (A₁ ≃ₐ[R] A₁) A₁ˣ where
  smul := fun f => Units.map f
  one_smul := fun x => by ext; rfl
  mul_smul := fun x y z => by ext; rfl
  smul_mul := fun x y z => by ext; exact x.map_mul _ _
  smul_one := fun x => by ext; exact x.map_one

@[simp]
theorem smul_units_def (f : A₁ ≃ₐ[R] A₁) (x : A₁ˣ) :
    f • x = Units.map f x := rfl

@[simp]
theorem algebraMap_eq_apply (e : A₁ ≃ₐ[R] A₂) {y : R} {x : A₁} :
    algebraMap R A₂ y = e x ↔ algebraMap R A₁ y = x :=
  ⟨fun h => by simpa using e.symm.toAlgHom.algebraMap_eq_apply h, fun h =>
    e.toAlgHom.algebraMap_eq_apply h⟩
#align alg_equiv.algebra_map_eq_apply AlgEquiv.algebraMap_eq_apply

/-- `AlgEquiv.toLinearMap` as a `MonoidHom`. -/
@[simps]
def toLinearMapHom (R A) [CommSemiring R] [Semiring A] [Algebra R A] :
    (A ≃ₐ[R] A) →* A →ₗ[R] A where
  toFun := AlgEquiv.toLinearMap
  map_one' := rfl
  map_mul' := fun _ _ ↦ rfl

lemma pow_toLinearMap (σ : A₁ ≃ₐ[R] A₁) (n : ℕ) :
    (σ ^ n).toLinearMap = σ.toLinearMap ^ n :=
  (AlgEquiv.toLinearMapHom R A₁).map_pow σ n

@[simp]
lemma one_toLinearMap :
    (1 : A₁ ≃ₐ[R] A₁).toLinearMap = 1 := rfl

/-- The units group of `S →ₐ[R] S` is `S ≃ₐ[R] S`.
See `LinearMap.GeneralLinearGroup.generalLinearEquiv` for the linear map version. -/
@[simps]
def algHomUnitsEquiv (R S : Type*) [CommSemiring R] [Semiring S] [Algebra R S] :
    (S →ₐ[R] S)ˣ ≃* (S ≃ₐ[R] S) where
  toFun := fun f ↦
    { (f : S →ₐ[R] S) with
      invFun := ↑(f⁻¹)
      left_inv := (fun x ↦ show (↑(f⁻¹ * f) : S →ₐ[R] S) x = x by rw [inv_mul_self]; rfl)
      right_inv := (fun x ↦ show (↑(f * f⁻¹) : S →ₐ[R] S) x = x by rw [mul_inv_self]; rfl) }
  invFun := fun f ↦ ⟨f, f.symm, f.comp_symm, f.symm_comp⟩
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl
  map_mul' := fun _ _ ↦ rfl

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A₁] [CommSemiring A₂]

variable [Algebra R A₁] [Algebra R A₂] (e : A₁ ≃ₐ[R] A₂)

-- Porting note: Added nonrec
nonrec theorem map_prod {ι : Type*} (f : ι → A₁) (s : Finset ι) :
    e (∏ x in s, f x) = ∏ x in s, e (f x) :=
  map_prod _ f s
#align alg_equiv.map_prod AlgEquiv.map_prod

-- Porting note: Added nonrec
nonrec theorem map_finsupp_prod {α : Type*} [Zero α] {ι : Type*} (f : ι →₀ α) (g : ι → α → A₁) :
    e (f.prod g) = f.prod fun i a => e (g i a) :=
  map_finsupp_prod _ f g
#align alg_equiv.map_finsupp_prod AlgEquiv.map_finsupp_prod

end CommSemiring

section Ring

variable [CommSemiring R] [Ring A₁] [Ring A₂]

variable [Algebra R A₁] [Algebra R A₂] (e : A₁ ≃ₐ[R] A₂)

protected theorem map_neg (x) : e (-x) = -e x :=
  map_neg e x
#align alg_equiv.map_neg AlgEquiv.map_neg

protected theorem map_sub (x y) : e (x - y) = e x - e y :=
  map_sub e x y
#align alg_equiv.map_sub AlgEquiv.map_sub

end Ring

end AlgEquiv

namespace MulSemiringAction

variable {M G : Type*} (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

section

variable [Group G] [MulSemiringAction G A] [SMulCommClass G R A]

/-- Each element of the group defines an algebra equivalence.

This is a stronger version of `MulSemiringAction.toRingEquiv` and
`DistribMulAction.toLinearEquiv`. -/
@[simps! apply symm_apply toEquiv] -- Porting note: don't want redundant simps lemma `toEquiv_symm`
def toAlgEquiv (g : G) : A ≃ₐ[R] A :=
  { MulSemiringAction.toRingEquiv _ _ g, MulSemiringAction.toAlgHom R A g with }
#align mul_semiring_action.to_alg_equiv MulSemiringAction.toAlgEquiv

theorem toAlgEquiv_injective [FaithfulSMul G A] :
    Function.Injective (MulSemiringAction.toAlgEquiv R A : G → A ≃ₐ[R] A) := fun _ _ h =>
  eq_of_smul_eq_smul fun r => AlgEquiv.ext_iff.1 h r
#align mul_semiring_action.to_alg_equiv_injective MulSemiringAction.toAlgEquiv_injective

end

end MulSemiringAction

end ValAlgHom_ValAlgEquiv
