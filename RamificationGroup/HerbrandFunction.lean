import RamificationGroup.Valued.Hom.Defs
import Mathlib.FieldTheory.Galois

open DiscreteValuation

namespace HerbrandFunction

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [ValAlgebra R S]

def phi (K L : Type*) [CommRing K] [Ring L] [Algebra K L] : ℚ → ℚ := sorry

scoped notation:max  " φ_[" L:max "/" K:max "]" => phi K L

def psi (K L : Type*) [CommRing K] [Ring L] [Algebra K L] : ℚ → ℚ := sorry

scoped notation:max  " ψ_[" L:max "/" K:max "]" => psi K L

variable (K L : Type*) [CommRing K] [Ring L] [Algebra K L] (x : ℕ)
#check φ_[L/K] x
#check ψ_[L/K] x
end HerbrandFunction
