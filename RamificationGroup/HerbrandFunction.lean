import RamificationGroup.Valued.Hom.Defs
import Mathlib.FieldTheory.Galois

open DiscreteValuation

namespace HerbrandFunction

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [ValAlgebra R S]

def phi (K L : Type*) [CommRing K] [Ring L] [Algebra K L] : ℚ → ℚ := sorry

-- scoped notation:max  " φ_[" L:max "/" K:max "]" => phi K L

def psi (K L : Type*) [CommRing K] [Ring L] [Algebra K L] : ℚ → ℚ := sorry

-- scoped notation:max  " ψ_[" L:max "/" K:max "]" => psi K L

-- this is not useful, see theorem below
theorem leftInverse_phi_psi (K L : Type*) [CommRing K] [Ring L] [Algebra K L] : Function.LeftInverse (psi K L) (phi K L)  := sorry

@[simp]
theorem phi_psi_eq_self (K L : Type*) [CommRing K] [Ring L] [Algebra K L] (u : ℚ) : (phi K L) ((psi K L) u) = u := leftInverse_phi_psi K L u

theorem phi_strictMono (K L : Type*) [CommRing K] [Ring L] [Algebra K L] : StrictMono (phi K L) := sorry

end HerbrandFunction
