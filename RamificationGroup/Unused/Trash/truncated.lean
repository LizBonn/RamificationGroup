import RamificationGroup.LowerNumbering

open DiscreteValuation Valued Valuation

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [ValAlgebra R S]

theorem lowerindex_ge_iff_lowerramificationGroup (s : (S ≃ₐv[R] S)) {i : ℕ} : i_[S/R] s ≥ i + 1 ↔ s ∈ G(S/R)_[i] := by sorry

theorem lowerindex_eq_iff_lowerramificationGroup (s : (S ≃ₐv[R] S)) {i : ℕ} : i_[S/R] s = i + 1 ↔ s ∈ G(S/R)_[i] ∧ s ∉ G(S/R)_[(i + 1)] := by sorry

theorem lowerramificationGroup_has_top : ∃ n₀ : ℕ , ∀ n : ℕ , n ≥ n₀ → G(S/R)_[n] = {1 : (S ≃ₐv[R] S)} := by sorry

noncomputable def ValAlgEquiv.TruncatedlowerIndex (s : (S ≃ₐv[R] S)) : ℕ :=
  sorry

scoped [DiscreteValuation] notation:max " i_[" S:max "/" R:max "]ₜ" => ValAlgEquiv.TruncatedlowerIndexlowerIndex R S

noncomputable def ValAlgEquiv.truncatedlowerIndex (s : (S ≃ₐv[R] S)) (u : ℕ): ℕ :=
  if h : i_[S/R] s = ⊤ then u
  else if (i_[S/R] s) > u then u
  else (i_[S/R] s).untop h
