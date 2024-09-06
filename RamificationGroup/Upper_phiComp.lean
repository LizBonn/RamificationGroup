import RamificationGroup.UpperNumbering

open QuotientGroup IntermediateField DiscreteValuation Valued Valuation HerbrandFunction

variable (μ : MeasureTheory.Measure ℝ)
variable (K K' L : Type*) {ΓK : outParam Type*} [Field K] [Field K'] [Field L] [vK' : Valued K' ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK'.v] [IsDiscrete vL.v] [Algebra K L] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L] [IsValExtension K' L] [Normal K K'] [Normal K L] [FiniteDimensional K L] [FiniteDimensional K K'] [FiniteDimensional K' L]

noncomputable def phiDerivReal (u : ℝ) : ℝ :=
  (Nat.card G(L/K)_[(max 0 ⌈u⌉)] : ℚ) / (Nat.card G(L/K)_[0] : ℚ)

noncomputable def phiReal (u : Real) : Real := intervalIntegral (phiDerivReal (K := K) (L := L)) 0 u μ

theorem continuous_phiDerivReal : Continuous (phiDerivReal (K := K) (L := L)) := by sorry

theorem phiReal_eq_phi {u : ℚ} : phiReal μ (K := K) (L := L) u = phi K L u := by sorry

theorem phiReal_zero_eq_zero : phiReal μ K L 0 = 0 := by sorry

noncomputable def phiDerivReal_lin : ℝ →L[ℝ] ℝ where
  toFun := phiDerivReal K L
  map_add' := sorry
  map_smul' := sorry
  cont := sorry

theorem phiReal_hasDeriv {x : ℝ} : HasFDerivAt (𝕜 := ℝ) (phiReal μ K L) (phiDerivReal_lin K L) x := by sorry

theorem phiReal_Defferentiable : Differentiable ℝ (phiReal μ K L) := by sorry

set_option maxHeartbeats 0

theorem phiReal_comp_of_isValExtension' (u : ℝ) : (phiReal μ (K := K) (L := K')) ∘ (phiReal μ (K := K') (L := L)) = phiReal μ (K := K) (L := L) := by
  apply eq_of_fderiv_eq (𝕜 := ℝ) (x := 0)
  · rw [Function.comp_apply, phiReal_zero_eq_zero, phiReal_zero_eq_zero, phiReal_zero_eq_zero]
  · apply Differentiable.comp (phiReal_Defferentiable μ K K') (phiReal_Defferentiable μ K' L)
  · apply phiReal_Defferentiable
  · intro x
    conv =>
      right
      rw [HasFDerivAt.fderiv (x := x) (by apply phiReal_hasDeriv μ K L)]
    rw [fderiv.comp, HasFDerivAt.fderiv (x := x) (by apply phiReal_hasDeriv μ K' L), HasFDerivAt.fderiv (x := (phiReal μ K' L x)) (by apply phiReal_hasDeriv μ K K')]
    ext
    unfold phiDerivReal_lin phiDerivReal
    simp only [Rat.cast_natCast, ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, Int.ceil_one, zero_le_one, max_eq_right]
    rw [max_eq_right]
    calc
      _ = (Nat.card G(K'/K)_[⌈phi K' L 1⌉] : ℚ) / (Nat.card G(K'/K)_[0] : ℚ) := by
        sorry
      _ = (Nat.card (G(L/K)_[⌈(1 : ℚ)⌉].map (AlgEquiv.restrictNormalHom K'))) / (Nat.card G(K'/K)_[0] : ℚ) := by
        sorry
      _ = _ := by
        sorry
    sorry
    sorry
    apply Differentiable.differentiableAt (phiReal_Defferentiable μ K K')
    apply Differentiable.differentiableAt (phiReal_Defferentiable μ K' L)


@[simp]
theorem phi_comp_of_isValExtension' (u : ℚ): (phi K K') ((phi K' L) u) = (phi K L) u := by
  have : ((phi K K') ((phi K' L) u) : ℝ) = ((phi K L) u  : ℝ) := by
    rw [← phiReal_eq_phi μ K L, ← phiReal_eq_phi μ K K', ← phiReal_eq_phi μ K' L, ← Function.comp_apply (f := phiReal μ K K')]
    rw [phiReal_comp_of_isValExtension' μ K K' L u]
  apply_mod_cast this
