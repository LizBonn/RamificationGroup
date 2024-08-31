import RamificationGroup.Herbrand_aux
import Mathlib.RingTheory.Valuation.Basic

open scoped Classical
open HerbrandFunction DiscreteValuation AlgEquiv Valued
open DiscreteValuation Subgroup Set Function Finset BigOperators Int Valued

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [vK : Valued K ℤₘ₀] [Valuation.IsDiscrete vK.v] [vL : Valued L ℤₘ₀] [Algebra K L] [IsValExtension K L] [FiniteDimensional K L] [CompleteSpace K] [Algebra.IsSeparable K L]
[Algebra.IsSeparable (LocalRing.ResidueField ↥𝒪[K]) (LocalRing.ResidueField ↥𝒪[L])]

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [Algebra R S]


theorem phi_linear_section_aux {n : ℤ} {x : ℚ} (hx : n ≤ x ∧ x < n + 1) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : phi K L x = phi K L n + (phi K L (n + 1) - phi K L n) * (x - n) := by
  by_cases hc : 0 < x
  · have hn : (0 : ℚ) ≤ n := by sorry
    by_cases hc' : (0 : ℚ) < n
    · rw [phi_eq_sum_card K L hc]
      nth_rw 1 [phi_eq_sum_card K L hc']
      sorry
    · have hn' : n = 0 := by sorry
      simp only [hn', cast_zero, zero_add, sub_zero]
      sorry
  · push_neg at hc
    rw [phi_eq_self_of_le_zero K L hc]
    sorry

theorem phi_Bijective_section_aux {n : ℤ} {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : ∀ (y : ℚ) , (phi K L n) ≤ y ∧ y < (phi K L (n + 1)) → ∃ (x : ℚ), phi K L x = y := by
  intro y ⟨hy1, hy2⟩
  use (n + ((y - phi K L n) / (phi K L (n + 1) - phi K L n)))
  have hx : n ≤ (n + ((y - phi K L n) / (phi K L (n + 1) - phi K L n))) ∧ (n + ((y - phi K L n) / (phi K L (n + 1) - phi K L n))) < n + 1 := by sorry
  rw [phi_linear_section_aux K L hx hgen]
  rw [add_comm (n : ℚ) ((y - phi K L n) / (phi K L (n + 1) - phi K L n)), add_sub_assoc, sub_self, add_zero, ]
  have :  (phi K L (↑n + 1) - phi K L ↑n) * ((y - phi K L ↑n) / (phi K L (↑n + 1) - phi K L ↑n)) = (y - phi K L y) := by sorry
  rw [this]

theorem phi_infty (y : ℚ) : ∃ n : ℤ, phi R S n ≤ y ∧ y < phi R S (n + 1) := by
  by_contra hc
  push_neg at hc
  have hz : ∀ n : ℤ, phi R S n ≤ y := by
    intro n
    sorry
  have hq : ∀ n : ℚ, phi R S n ≤ y := by
    intro n
    apply le_trans (b := phi R S ⌈n⌉)
    · by_cases hc : n = ⌈n⌉
      · rw [← hc]
      · apply le_of_lt; apply phi_strictMono R S _
        apply lt_of_le_of_ne; apply Int.le_ceil; exact hc
    · apply hz ⌈n⌉
  sorry

theorem phi_Bijective_aux : Function.Bijective (phi R S) := by
  constructor
  · rintro a1 a2 h
    contrapose! h
    by_cases h1 : a1 > a2
    · apply ne_of_gt (phi_strictMono R S h1)
    · push_neg at *
      apply ne_of_lt (phi_strictMono R S (lt_of_le_of_ne h1 h))
  · rintro y
    obtain ⟨n, hn⟩ := phi_infty R S y
    apply phi_Bijective_section_aux R S (n := n) y hn
