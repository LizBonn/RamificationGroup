import RamificationGroup.Valued.Defs

open DiscreteValuation Valuation

section Hom

/-- `ValRingHom A B` is the type of ring homomorphisms that preserves valuation from valued ring `A` to valued ring `B`.

When possible, instead of parametrizing results over `(f : ValRingHom α β)`,
you should parametrize over `(F : Type*) [ValRingHomClass F α β] (f : F)`.

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

@[inherit_doc]
infixr:25 " →+*v " => ValRingHom -- 25 = Binding power of `→+*`

/-- `ValRingEquiv A B` is the type of ring isomorphisms that preserves valuation from valued ring `A` to valued ring `B`.

When possible, instead of parametrizing results over `(f : ValRingEquiv α β)`,
you should parametrize over `(F : Type*) [ValRingEquivClass F α β] (f : F)`.

When you extend this structure, make sure to extend `ValRingEquivClass`.
-/
structure ValRingEquiv (R S : Type*) {ΓR ΓS : outParam Type*} [Ring R] [Ring S]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS]
  [vR : Valued R ΓR] [vS : Valued S ΓS]
  extends OrderRingIso R S, Homeomorph R S where
  val_isEquiv_comap' : vR.v.IsEquiv (vS.v.comap toRingEquiv)

@[inherit_doc]
infixr:25 " ≃+*v " => ValRingEquiv

end Hom

section Class

/-- `ValHomClass F α b` asserts that `F` is a type of valuation-preserving morphisms. -/
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

end Class

-- `theorem of ValRingEquivClass, about inv preserves valuation, in section class `

/-
section LE

variable [LE α] [LE β] [EquivLike F α β] [OrderIsoClass F α β]

-- Porting note: needed to add explicit arguments to map_le_map_iff
@[simp]
theorem map_inv_le_iff (f : F) {a : α} {b : β} : EquivLike.inv f b ≤ a ↔ b ≤ f a := by
  convert (map_le_map_iff f (a := EquivLike.inv f b) (b := a)).symm
  exact (EquivLike.right_inv f _).symm
#align map_inv_le_iff map_inv_le_iff

-- Porting note: needed to add explicit arguments to map_le_map_iff
@[simp]
theorem le_map_inv_iff (f : F) {a : α} {b : β} : a ≤ EquivLike.inv f b ↔ f a ≤ b := by
  convert (map_le_map_iff f (a := a) (b := EquivLike.inv f b)).symm
  exact (EquivLike.right_inv _ _).symm
#align le_map_inv_iff le_map_inv_iff

end LE
-/

-- `relation between v and f, in section class`

/-
variable [Preorder α] [Preorder β] [EquivLike F α β] [OrderIsoClass F α β]

theorem map_lt_map_iff (f : F) {a b : α} : f a < f b ↔ a < b :=
  lt_iff_lt_of_le_iff_le' (map_le_map_iff f) (map_le_map_iff f)
#align map_lt_map_iff map_lt_map_iff

@[simp]
theorem map_inv_lt_iff (f : F) {a : α} {b : β} : EquivLike.inv f b < a ↔ b < f a := by
  rw [← map_lt_map_iff f]
  simp only [EquivLike.apply_inv_apply]
#align map_inv_lt_iff map_inv_lt_iff

@[simp]
theorem lt_map_inv_iff (f : F) {a : α} {b : β} : a < EquivLike.inv f b ↔ f a < b := by
  rw [← map_lt_map_iff f]
  simp only [EquivLike.apply_inv_apply]
#align lt_map_inv_iff lt_map_inv_iff
-/

namespace ValRingHom

end ValRingHom

namespace ValRingEquiv

end ValRingEquiv

section

variable {R S : Type*} {ΓR ΓS : outParam Type*} [Ring R] [Ring S]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS]
  [vR : Valued R ΓR] [vS : Valued S ΓS]

def ValRingHom.mk' (f : R →+* S) (hf : vR.v.IsEquiv (vS.v.comap f)) : R →+*v S where
  toRingHom := f
  monotone' := sorry -- add a theorem for this at the begining
  val_isEquiv_comap' := hf
  continuous_toFun := sorry -- add a theorem for this at the begining

def ValRingEquiv.mk' (f : R ≃+* S) (hf : vR.v.IsEquiv (vS.v.comap f)) : R ≃+*v S where
  toRingEquiv := f
  map_le_map_iff' := sorry
  continuous_toFun := sorry
  continuous_invFun := sorry
  val_isEquiv_comap' := sorry

-- ValRingHomClass
-- ValRingIsoClass

-- `copy lemmas in OrderRingHom`
-- `id, comp`
-- `OrderRingIso.symm`

protected def ValRingHom.id : (R →+*v R) where
  toOrderRingHom := .id R
  continuous_toFun := continuous_id
  val_isEquiv_comap' := IsEquiv.refl

@[refl]
protected def ValRingEquiv.refl : (R ≃+*v R) where
  toOrderRingIso := .refl R
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id
  val_isEquiv_comap' := IsEquiv.refl


attribute [coe] ValRingHom.toOrderRingHom

/- @[coe]
def ValRingHom.toRingHom' (f : R →+*v S) : (R →+* S) := f.toRingHom
-/

instance : Coe (R →+*v S) (R →+*o S) := ⟨ValRingHom.toOrderRingHom⟩

instance : Coe (R →+*v S) (R →+* S) := ⟨fun f => f.toRingHom⟩

@[coe]
def ValRingEquiv.toValRingHom (f : R ≃+*v S) : R →+*v S := ⟨f.toOrderRingHom, f.continuous_toFun, f.val_isEquiv_comap'⟩

instance : Coe (R ≃+*v S) (R →+*v S) := ⟨ValRingEquiv.toValRingHom⟩ -- `This is temporory, should Mimic instCoeTCOrderRingHom, use ValRingHomClass to implement this`
/-
variable {α β} [OrderedRing α] [OrderedRing β] (f : α ≃+*o β)
#synth CoeTC (α ≃+*o β)  (α →+*o β) -- instCoeTCOrderRingHom
#check (f : OrderRingHom α β)
-/

instance : Coe (R ≃+*v S) (R ≃+*o S) := ⟨ValRingEquiv.toOrderRingIso⟩

instance : Coe (R ≃+*v S) (R ≃+* S) := ⟨fun f => f.toRingEquiv⟩

-- `for ValRingEquiv`

instance : FunLike (ValRingHom R S) R S where
  coe f := f.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨_, _⟩, _⟩
    rcases g with ⟨⟨_, _⟩, _⟩
    dsimp at h
    congr
    apply DFunLike.coe_injective'
    exact h

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
    apply DFunLike.coe_injective'
    exact h

end

section

class ValAlgebra (R A : Type*) {ΓR ΓA : outParam Type*} [CommRing R] [Ring A] [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [vR : Valued R ΓR] [vA : Valued A ΓA] extends ValRingHom R A, Algebra R A

-- do not use this... definitional equal problems
def ValRingHom.toValAlgebra {R A : Type*} {ΓR ΓA : outParam Type*} [CommRing R] [CommRing A] [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [Valued R ΓR] [Valued A ΓA] (f : R →+*v A) : ValAlgebra R A where
  toValRingHom := f
  smul := f.toRingHom.toAlgebra.smul
  smul_def' := f.toRingHom.toAlgebra.smul_def'
  commutes' := f.toRingHom.toAlgebra.commutes'

-- `copy more lemmas in Algebra`

def valAlgebraMap (R A : Type*) {ΓR ΓA : outParam Type*} [CommRing R] [CommRing A] [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [Valued R ΓR] [Valued A ΓA] [ValAlgebra R A] : R →+*v A := ValAlgebra.toValRingHom (R := R) (A := A)

end

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
  monotone' := f.toValRingHom.monotone'
  continuous_toFun := f.toValRingHom.continuous_toFun
  val_isEquiv_comap' := f.toValRingHom.val_isEquiv_comap'
  commutes' := f.commutes'

instance : CoeTC (A ≃ₐv[R] B) (A →ₐv[R] B) := ⟨ValAlgEquiv.toValAlgHom⟩
-- `This is temporory, should Mimic instCoeTCOrderRingHom, use ValAlgHomClass to implement this coe instance`
/-
variable {α β} [OrderedRing α] [OrderedRing β] (f : α ≃+*o β)
#synth CoeTC (α ≃+*o β)  (α →+*o β) -- instCoeTCOrderRingHom
#check (f : OrderRingHom α β)
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

-- -- structures on ValRingIso
instance {A : Type*} [Ring A] {ΓA : outParam Type*} [LinearOrderedCommGroupWithZero ΓA] [Valued A ΓA]: Group (A ≃+*v A) where
  mul := sorry
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  inv := sorry
  mul_left_inv := sorry

instance {R A : Type*} [CommRing R] [Ring A] {ΓR ΓA : outParam Type*} [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] [Valued R ΓR] [Valued A ΓA] [ValAlgebra R A] : Group (A ≃ₐv[R] A) where
  mul := sorry
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  inv := sorry
  mul_left_inv := sorry
