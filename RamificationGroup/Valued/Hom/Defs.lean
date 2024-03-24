import RamificationGroup.Valued.Defs

-- `Big Question: Should be ValRingHom only requires v x ≤ v y → v f x ≤ v f y , or iff???` Maybe first is better?
-- `Consider K → K [[X]] , K is a local field, K[X] with valuation trivial on K, valuation ideal given by (X). This satisfies v x ≤ v y → v f x ≤ v f y`
-- if the first definition K of local field K can have many valuation on L. second  will pin down the valuation on L
-- if as first choice, order preserving <=> valuation preserving <=> continuous (v(x) < 1 -> v f x < 1, by x^n -> 0 -> f x ^n -> 0)
-- preorder on the set of valuations? not a type, IsSpecialization
open DiscreteValuation Valuation Valued

section ValRingHom_ValRingEquiv

section Hom

-- Valuation on B is an extension of valuation on A.
/-- `ValRingHom R S` is the type of ring homomorphisms that preserves valuation from valued ring `A` to valued ring `B`. Please note that the definition requires `v x ≤ v y ↔ v (f x) ≤ v (f y)` instead of `v x ≤ v y → v (f x) ≤ v (f y)`. For the latter case, one can use order-preserving ring homomorphisms.

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
  [vR : Valued R ΓR] [vS : Valued S ΓS] [FunLike F R S] extends RelHomClass F ((· ≤ ·) : R → R → Prop) ((· ≤ ·) : S → S → Prop), RingHomClass F R S, ContinuousMapClass F R S where
  val_isEquiv_comap (f : F) : vR.v.IsEquiv (vS.v.comap f)

export ValRingHomClass (val_isEquiv_comap)

class ValRingEquivClass (F R S : Type*) {ΓR ΓS : outParam Type*} [Ring R] [Ring S]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS]
  [vR : Valued R ΓR] [vS : Valued S ΓS] [EquivLike F R S] extends OrderIsoClass F R S, RingEquivClass F R S, ContinuousMapClass F R S where
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

class ValAlgebra (R A : Type*) {ΓR ΓA : outParam Type*} [CommRing R] [Ring A] [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [vR : Valued R ΓR] [vA : Valued A ΓA] extends ValRingHom R A, Algebra R A

-- do not use this... definitional equal problems
def ValRingHom.toValAlgebra {R A : Type*} {ΓR ΓA : outParam Type*} [CommRing R] [CommRing A] [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [Valued R ΓR] [Valued A ΓA] (f : R →+*v A) : ValAlgebra R A where
  toValRingHom := f
  smul := f.toRingHom.toAlgebra.smul
  smul_def' := f.toRingHom.toAlgebra.smul_def'
  commutes' := f.toRingHom.toAlgebra.commutes'

-- `copy more lemmas in Algebra`

def valAlgebraMap (R A : Type*) {ΓR ΓA : outParam Type*} [CommRing R] [CommRing A] [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [Valued R ΓR] [Valued A ΓA] [ValAlgebra R A] : R →+*v A := ValAlgebra.toValRingHom (R := R) (A := A)

end ValAlgebra

section

variable (R A B : Type*) [CommRing R] [Ring A] [Ring B] {ΓR ΓA ΓB : outParam Type*} [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [LinearOrderedCommGroupWithZero ΓB] [Valued R ΓR] [vA : Valued A ΓA] [vB : Valued B ΓB] [ValAlgebra R A] [ValAlgebra R B]

structure ValAlgHom extends ValRingHom A B, AlgHom R A B

structure ValAlgEquiv extends ValRingEquiv A B, AlgEquiv R A B

notation:25 A " →ₐv[" R "] " B => ValAlgHom R A B

notation:25 A " ≃ₐv[" R "] " B => ValAlgEquiv R A B

-- ValAlgHomClass
-- ValAlgIsoClass

end

section

variable {R A B : Type*} [CommRing R] [Ring A] [Ring B] {ΓR ΓA ΓB : outParam Type*} [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [LinearOrderedCommGroupWithZero ΓB] [Valued R ΓR] [vA : Valued A ΓA] [vB : Valued B ΓB] [fA : ValAlgebra R A] [fB : ValAlgebra R B]

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
section coercion
-- -- coercions

variable {R A B : Type*} [CommRing R] [Ring A] [Ring B] {ΓR ΓA ΓB : outParam Type*} [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [LinearOrderedCommGroupWithZero ΓB] [Valued R ΓR] [Valued A ΓA] [Valued B ΓB] [ValAlgebra R A] [ValAlgebra R B]

instance ValAlgHom.algHom : Coe (A →ₐv[R] B) (A →ₐ[R] B) := ⟨ValAlgHom.toAlgHom⟩

instance ValAlgEquiv.algEquiv: Coe (A ≃ₐv[R] B) (A ≃ₐ[R] B) := ⟨ValAlgEquiv.toAlgEquiv⟩

instance : CoeTC (A →ₐv[R] B) (A →+*v B) := ⟨ValAlgHom.toValRingHom⟩

instance : CoeTC (A ≃ₐv[R] B) (A ≃+*v B) := ⟨ValAlgEquiv.toValRingEquiv⟩
-- `This is temporory, should mimic instCoeTCRingHom use ValRingHomClass to achieve this`
/-
#synth CoeTC (AlgHom R A B) (RingHom A B)
#check instCoeTCRingHom
-/

def ValAlgEquiv.toValAlgHom (f : A ≃ₐv[R] B) : (A →ₐv[R] B) where
  toFun := f.toFun
  map_one' := f.map_one
  map_mul' := f.map_mul
  map_zero' := f.map_zero
  map_add' := f.map_add
  monotone' := by exact OrderHom.monotone (f.toValRingEquiv : A →o B)
  continuous_toFun := f.toValRingEquiv.continuous_toFun
  val_isEquiv_comap' := f.toValRingEquiv.val_isEquiv_comap'
  commutes' := f.commutes'

instance : CoeTC (A ≃ₐv[R] B) (A →ₐv[R] B) := ⟨ValAlgEquiv.toValAlgHom⟩
-- `This is temporory, should Mimic instCoeTCOrderRingHom, use ValAlgHomClass to implement this coe instance`
/-
variable {R S} [OrderedRing R] [OrderedRing S] (f : R ≃+*o S)
#synth CoeTC (R ≃+*o S)  (R →+*o S) -- instCoeTCOrderRingHom
#check (f : OrderRingHom R S)
-/

end coercion

variable {R A B : Type*} [CommRing R] [Ring A] [Ring B] {ΓR ΓA ΓB : outParam Type*} [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [LinearOrderedCommGroupWithZero ΓB] [Valued R ΓR] [Valued A ΓA] [Valued B ΓB] [ValAlgebra R A] [ValAlgebra R B]

#synth Algebra R A
#synth CoeFun (AlgEquiv R A B) (fun _ => (A → B))

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
