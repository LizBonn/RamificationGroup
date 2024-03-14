import RamificationGroup.Unused.Definition.ExtensionOfValuation
import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.FieldTheory.Galois


-- rename this file to RamificationFiltration or something

-- `Mathlib.RingTheory.Ideal.QuotientOperations`
-- def AlgHom.QuotientLift {R S₁ S₂ : Type*} [CommRing R] [CommRing S₁] [CommRing S₂] [Algebra R S₁] [Algebra R S₂] {I : Ideal R} {J₁ : Ideal S₁} {J₂ : Ideal S₂} (h₁ : I ≤ J₁.comap (algebraMap R S₁)) (h₂ : I ≤ J₂.comap (algebraMap R S₂)) : S₁⧸J₁ →ₐ[R⧸I] S₂⧸J₂ := sorry

open DiscreteValuation

section
-- An alternative thought on definition of ValuationExtension


-- Maybe use `Valued` here is far better, Valued K + Finite K L will automatically create some ValuationExtension K L, However, this need to rewrite the definition of ValuationExtension

class ValuationExtension'' (K L : Type*) [Field K] [Field L] {ΓK: outParam (Type*)} {ΓL : outParam (Type*)} [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL] [Valued K ΓK] [Valued L ΓL] where
  toAlgebra : Algebra K L
  val_extn : PreserveValuation Valued.v Valued.v (algebraMap K L)

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Valued K ℤₘ₀] [Valued L ℤₘ₀]
#check ValuationExtension'' K L

-- And there is Valued instance on K L!
-- Maybe ValuationExtension is not a good name...

notation:max K:max " →ᵥ " L:max => ValuationExtension'' K L
-- or "→+*ᵥ"

-- divide into 2 parts,  ` →ᵥ ` and `ValuedAlgebra`, first is the set of all possible maps preserving valuation, second is when there is a canonical map

instance : Coe (ValuationExtension'' K L) (Algebra K L) :=
  ⟨fun f => f.toAlgebra⟩

instance : CoeFun (ValuationExtension'' K L) (fun _ => K → L) := sorry

variable (f : K →ᵥ L) (k : K)
#check f k

-- ValuedScalarTower, automated infered from other instances
end

section

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (vK : Valuation K ℤₘ₀) (vL : Valuation L ℤₘ₀) [ValuationExtension vK vL] --some more condition to make sure vL(pi) = 1, probably uniformizer, same as Maria's definition

def Valuation.ramificationIndex (vK : Valuation K ℤₘ₀) (vL : Valuation L ℤₘ₀) [ValuationExtension vK vL] : ℤ := sorry -- Or it is possible to use other people's definition, here just a theorem relate its relation with valuation of the uniformizer

notation:max " e(" vL:max "/" vK:max ") " => Valuation.ramificationIndex vK vL

#check 𝓂[vL]

-- `theorem TFAE`
-- fix O / m^i
-- ∀ a : 𝒪[vL], vL ( a - s a) >= i
-- generator x, vL(x - sx) >= i

instance: Coe ℤ (Multiplicative ℤ) := ⟨fun x => x⟩

variable {G : Type*} [Group G]

#synth CoeTC G (WithZero G)
instance : Coe ℤ ℤₘ₀ := ⟨fun x => ((x : Multiplicative ℤ): WithZero ℤ) ⟩

def DiscreteValuation.toInt (i : ℤₘ₀) : WithTop ℤ := sorry
variable (i : ℤₘ₀)
#check toInt i

-- a general instance? for well founded orders
instance : InfSet (WithTop ℤ) := sorry

def lowerIndex (s : L ≃ₐ[K] L) : WithTop ℤ := iInf (fun x : 𝒪[vL] => toInt (vL (s.liftValuationInteger vK vL x - x))) -1

def RamificationGroup (i : ℤ) : Subgroup (L ≃ₐ[K] L) where
  carrier := --{s : L ≃ₐ[K] L | ∀ x : 𝒪[vL], toInt (vL (s.liftValuationInteger vK vL x - x)) ≥ i + 1 }
    {s :  L ≃ₐ[K] L | lowerIndex vK vL s ≥ i}
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

notation:max " i[" vL:max "/" vK:max "]" => lowerIndex vK vL

notation:max " G(" vL:max "/" vK:max ")_[" n:max "] " => RamificationGroup vK vL n


#check i[vL/vK]
#check G(vL/vK)_[1]



-- Many properties
-- `i <=1, = ⊤` `the filtration is complete`

-- currently there is no subgroup filtration, only ideal filtration, maybe to define it is useful.
-- `the filtration is decreasing, and seperable`

end

section

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (K' : IntermediateField K L) [IsGalois K L] (vK : Valuation K ℤₘ₀) (vK' : Valuation K' ℤₘ₀) (vL : Valuation L ℤₘ₀) [ValuationExtension vK vL] [ValuationExtension vK' vL] --some more condition

-- `key theorem : lower numbering is compatible with subgroup` restate this into a better form...
theorem lower_numbering_inf (i : ℤ) : ((G(vL/vK)_[i]).subgroupOf K'.fixingSubgroup ).map (IntermediateField.fixingSubgroupEquiv K') = G(vL/vK')_[i] := sorry

theorem index_subgroup (s : K'.fixingSubgroup) : i[vL/vK'] (K'.fixingSubgroupEquiv s)  = i[vL/vK] s := sorry


variable [Normal K K'] [ValuationExtension vK vK'] --this should be later changed in to a scalar-tower-like instance
variable [FiniteDimensional K L]
#synth FiniteDimensional K K'
#synth Finite (L ≃ₐ[K] L)
#synth Finite (K' ≃ₐ[K] K')

open BigOperators

-- need instances of computation rules related to WithTop ℤ
instance : Coe (WithTop ℤ) (WithTop ℚ) := sorry
#synth Mul (WithTop ℚ)
theorem index_quotient_group (s₀ : L ≃ₐ[K] L) : i[vK'/vK] (s₀.restrictNormal K')  = ((1 / e(vL/vK) :ℚ) : (WithTop ℚ)) * ∑ s in {s : L ≃ₐ[K] L | s.restrictNormal K' = s₀.restrictNormal K'}.toFinite.toFinset, i[vL/vK] s := sorry
-- do we need to def this index finset separately?
end
