import RamificationGroup.Definition.CompleteValuationRing



variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]

-- #synth Algebra R T

variable {R S : Type*} [CommRing R] [CommRing S] {I : Ideal R} {J : Ideal S} [Algebra R S] (h : I ≤ J.comap (algebraMap R S))

-- #synth Algebra (R⧸I) (S⧸J)


-- `Mathlib.RingTheory.Ideal.QuotientOperations`
-- def AlgHom.QuotientLift {R S₁ S₂ : Type*} [CommRing R] [CommRing S₁] [CommRing S₂] [Algebra R S₁] [Algebra R S₂] {I : Ideal R} {J₁ : Ideal S₁} {J₂ : Ideal S₂} (h₁ : I ≤ J₁.comap (algebraMap R S₁)) (h₂ : I ≤ J₂.comap (algebraMap R S₂)) : S₁⧸J₁ →ₐ[R⧸I] S₂⧸J₂ := sorry


section
-- `move to MissingPieces`
variable {K L : Type*} [Field K] [Field L] {ΓK ΓL : Type*} [LinearOrderedCommGroupWithZero ΓK][LinearOrderedCommGroupWithZero ΓL] [Algebra K L] {vK : Valuation K ΓK} {vL : Valuation L ΓL}

instance : ValuationRing vK.integer where
  cond' := sorry

-- `the maximal ideal = the lt ideal`

#check 𝒪[vK]
#check 𝔪[vK]
#check 𝔪[vL]

end

section
open DiscreteValuation
#check ℕₘ₀

#synth LinearOrderedAddCommGroup ℤ

#synth LinearOrderedCommMonoidWithZero ℤₘ₀
#synth LinearOrderedCommGroupWithZero ℤₘ₀

#synth LinearOrderedCommMonoid (Multiplicative ℤ)

instance : LinearOrderedCommGroup (Multiplicative ℤ) := sorry

#synth LinearOrderedCommGroupWithZero ℤₘ₀

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {vL : Valuation L ℤₘ₀}

#check 𝔪[vL]

-- O / m^i
-- vL ( a - s a) -- quotient action

end
