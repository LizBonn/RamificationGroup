import RamificationGroup.HerbrandFunction.Bijection

namespace HerbrandFunction
open Function DiscreteValuation Valuation Valued

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [Algebra R S]

noncomputable def psi : ℚ → ℚ :=
  invFun (phi R S)

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [vK : Valued K ℤₘ₀] [Valuation.IsDiscrete vK.v] [vL : Valued L ℤₘ₀] [Valuation.IsDiscrete vL.v] [IsValExtension vK.v vL.v] [CompleteSpace K] [Algebra.IsSeparable K L]
[Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])]

theorem psi_bij {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : Function.Bijective (psi K L) := by
  constructor
  have hpsi: (invFun (phi K L)).Injective :=
    (rightInverse_invFun (phi_Bijective_aux K L hgen).2).injective
  exact hpsi
  apply invFun_surjective
  apply (phi_Bijective_aux K L hgen).1


noncomputable def psi' (v : ℚ): ℚ :=
  1 / (phiDeriv K L (psi K L v))

theorem psi_zero_eq_zero {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : psi K L 0 = 0 := by
  unfold psi
  nth_rw 1 [← phi_zero_eq_zero K L]
  have : id 0 = (0 : ℚ) := by rfl
  nth_rw 2 [← this]
  have Inj : (phi K L).Injective := by apply (phi_Bijective_aux K L hgen).1
  rw [← invFun_comp Inj]
  simp

theorem leftInverse_phi_psi {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : Function.LeftInverse (phi K L) (psi K L)  := by
  rintro a
  apply invFun_eq
  apply (phi_Bijective_aux K L hgen).surjective

@[simp]
theorem phi_psi_eq_self (u : ℚ) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : (phi K L) ((psi K L) u) = u := leftInverse_phi_psi K L hgen u


@[simp]
theorem psi_phi_eq_self (u : ℚ) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : (psi K L) ((phi K L) u) = u := by
  rw [← Function.comp_apply (f := psi K L) (g := phi K L)]
  unfold psi
  rw [Function.invFun_comp (f := (phi K L))]
  rfl; apply (phi_Bijective_aux K L hgen).injective


theorem psi_eq_self_of_le_neg_one {v : ℚ} (hv : v ≤ 0) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : psi K L v = v := by
  have h1 : phi K L (psi K L v) = v := by apply phi_psi_eq_self K L _ hgen
  have h2 : phi K L v = v := by apply phi_eq_self_of_le_zero K L hv
  apply (phi_Bijective_aux K L hgen).injective
  simp [h1, h2]


variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [Algebra R S]

variable (S' : Type*) [Ring S'] [vS' : Valued S' ℤₘ₀] [Algebra R S']
theorem phi_eq_ofEquiv {f : S ≃ₐ[R] S'} (hf : ∀ a : S, v a = v (f a)) (u : ℚ) : phi R S u = phi R S' u := by
  unfold phi phiDeriv lowerRamificationGroup
  simp only [hf]
  sorry

theorem psi_eq_ofEquiv {f : S ≃ₐ[R] S'} (hf : ∀ a : S, v a = v (f a)) (u : ℚ) : psi R S u = psi R S' u := by
  simp only [psi]
  congr
  ext u
  rw [phi_eq_ofEquiv R S S' hf]
