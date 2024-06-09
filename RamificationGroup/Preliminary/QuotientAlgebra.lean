import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.RingTheory.Ideal.Over

variable {R S : Type*} [CommRing R] [CommRing S] {I : Ideal R} {J : Ideal S} [Algebra R S]

def Ideal.quotientAlgebra' (h : I ≤ RingHom.ker (algebraMap R S)) : Algebra (R⧸I) S := (Ideal.Quotient.lift _ _ h).toAlgebra

-- Maybe we should just keep this ignored
instance [h : Fact (I ≤ RingHom.ker (algebraMap R S))] : Algebra (R⧸I) S := Ideal.quotientAlgebra' h.out

-- variable {S₁ S₂ : Type*} [CommRing S₁] [CommRing S₂] [Algebra R S₁] [Algebra R S₂] {I : Ideal R} {J₁ : Ideal S₁} {J₂ : Ideal S₂}

-- def AlgHom.Quotient₂ (s : S₁ →ₐ[R] S₂) (h : J₁ ≤ J₂.comap s) : S₁⧸J₁ →ₐ[R] S₂⧸J₂ := Ideal.quotientMapₐ _ s h

#check Ideal.quotientMapₐ
#check Ideal.Quotient.algebraQuotientOfLEComap

variable [Ideal.IsMaximal I]
-- #synth Field (R⧸I)
#check Ideal.Quotient.field
