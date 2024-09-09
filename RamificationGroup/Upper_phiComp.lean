import RamificationGroup.UpperNumbering

open QuotientGroup IntermediateField DiscreteValuation Valued Valuation HerbrandFunction

variable (μ : MeasureTheory.Measure ℝ)
variable (K K' L : Type*) {ΓK : outParam Type*} [Field K] [Field K'] [Field L] [vK : Valued K ℤₘ₀] [vK' : Valued K' ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK'.v] [IsDiscrete vL.v] [Algebra K L] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L] [IsValExtension K K'] [IsValExtension K' L] [IsValExtension K L] [Normal K K'] [Normal K L] [FiniteDimensional K L] [FiniteDimensional K K'] [FiniteDimensional K' L]


noncomputable def phiDerivReal (u : ℝ) : ℝ :=
  (Nat.card G(L/K)_[(max 0 ⌈u⌉)] : ℚ) / (Nat.card G(L/K)_[0] : ℚ)

noncomputable def phiReal (u : Real) : Real := intervalIntegral (phiDerivReal (K := K) (L := L)) 0 u μ

theorem continuous_phiDerivReal : Continuous (phiDerivReal (K := K) (L := L)) := by sorry

theorem phiReal_eq_phi {u : ℚ} : phiReal μ (K := K) (L := L) u = phi K L u := by sorry

theorem phiReal_zero_eq_zero : phiReal μ K L 0 = 0 := by sorry

-- noncomputable def phiDerivReal_lin : ℝ →L[ℝ] ℝ where
--   toFun := phiDerivReal K L
--   map_add' := sorry
--   map_smul' := sorry
--   cont := sorry

theorem phiReal_hasDeriv {x : ℝ} : HasDerivAt (phiReal μ K L) (phiDerivReal K L x) x := by sorry

theorem phiReal_Defferentiable : Differentiable ℝ (phiReal μ K L) := by sorry


-- theorem aux_2 : ↑(Nat.card ↥ G(K'/K)_[⌈(Nat.card ↥ G(L/K')_[1] : ℝ) / ↑(Nat.card ↥ G(L/K')_[0] : ℝ)⌉] ) / ↑(Nat.card ↥ G(K'/K)_[0] : ℝ) =
--   ↑(Nat.card ↥ G(L/K)_[1] : ℝ) / ↑(Nat.card ↥ G(L/K)_[0] : ℝ) := by
--       calc
--       _ = (Nat.card G(K'/K)_[⌈phi K' L 1⌉] : ℝ) / (Nat.card G(K'/K)_[0] : ℝ) := by
--         sorry
--       _ = (Nat.card (G(L/K)_[⌈(1 : ℚ)⌉].map (AlgEquiv.restrictNormalHom K'))) / (Nat.card G(K'/K)_[0] : ℝ) := by
--         sorry
--       _ = (Nat.card G(L/K)_[1] : ℝ) / (Nat.card G(L/K)_[0] : ℝ) := by
--         sorry

set_option maxHeartbeats 0

theorem RamificationGroup_card_comp_aux {x : ℝ} : (Nat.card (Subgroup.map (AlgEquiv.restrictNormalHom K') G(L/K)_[⌈x⌉]) : ℝ) * (Nat.card G(L/K')_[⌈x⌉] : ℝ) = (Nat.card G(L/K)_[⌈x⌉] : ℝ) := by sorry

theorem RamificationGroup_card_zero_comp_aux : (Nat.card G(K'/K)_[0] : ℝ) * (Nat.card G(L/K')_[0] : ℝ) = (Nat.card G(L/K)_[0] : ℝ) := by
  repeat rw [RamificationIdx_eq_card_of_inertia_group]
  sorry

theorem herbrand_Real (u : ℝ) : G(L/K)_[⌈u⌉].map (AlgEquiv.restrictNormalHom K') = G(K'/K)_[⌈phiReal μ K' L u⌉] := by sorry

theorem phiReal_comp_of_isValExtension' (u : ℝ) : (phiReal μ K K') ∘ (phiReal μ K' L) = phiReal μ K L := by
  apply eq_of_fderiv_eq (𝕜 := ℝ) (x := 0)
  · rw [Function.comp_apply, phiReal_zero_eq_zero, phiReal_zero_eq_zero, phiReal_zero_eq_zero]
  · apply Differentiable.comp (phiReal_Defferentiable μ K K') (phiReal_Defferentiable μ K' L)
  · apply phiReal_Defferentiable
  · intro x
    conv =>
      right
      rw [HasFDerivAt.fderiv (x := x) (by apply phiReal_hasDeriv μ K L)]
    ext
    rw [fderiv_deriv, deriv.comp, HasDerivAt.deriv (x := x) (by apply phiReal_hasDeriv μ K' L), HasDerivAt.deriv (x := (phiReal μ K' L x)) (by apply phiReal_hasDeriv μ K K')]
    -- conv =>
    --   enter [1, 2]
    --   rw [HasDerivAt.deriv]
    -- rw [fderiv.comp, HasFDerivAt.fderiv (x := x) (by apply phiReal_hasDeriv μ K' L), HasFDerivAt.fderiv (x := (phiReal μ K' L x)) (by apply phiReal_hasDeriv μ K K')]
    -- ext
    unfold phiDerivReal
    simp only [Rat.cast_natCast, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, smul_eq_mul, one_mul]
    --rw [max_eq_right]
    --apply aux_2 K K' L
    by_cases hc : ⌈x⌉ < 0
    · have hc' : ⌈(phiReal μ K' L x)⌉ < 0 := by sorry
      rw [max_eq_left (le_of_lt hc), max_eq_left (le_of_lt hc'), div_self, div_self, div_self, one_mul]
      repeat sorry
    · push_neg at hc
      have hc' : 0 ≤ ⌈(phiReal μ K' L x)⌉ := by sorry
      rw [max_eq_right hc, max_eq_right hc']
      calc
        _ = (Nat.card (G(L/K)_[⌈x⌉].map (AlgEquiv.restrictNormalHom K')) : ℝ) * (Nat.card G(L/K')_[⌈x⌉] : ℝ) / ((Nat.card G(K'/K)_[0] : ℝ) * (Nat.card G(L/K')_[0] : ℝ)) := by
          rw [← mul_div_mul_comm]
          congr
          rw [herbrand_Real]
        _ = _ := by
          congr
          apply RamificationGroup_card_comp_aux K K' L
          apply RamificationGroup_card_zero_comp_aux K K'
    apply Differentiable.differentiableAt (phiReal_Defferentiable μ K K')
    apply Differentiable.differentiableAt (phiReal_Defferentiable μ K' L)



@[simp]
theorem phi_comp_of_isValExtension' (u : ℚ): (phi K K') ((phi K' L) u) = (phi K L) u := by
  have : ((phi K K') ((phi K' L) u) : ℝ) = ((phi K L) u  : ℝ) := by
    rw [← phiReal_eq_phi μ K L, ← phiReal_eq_phi μ K K', ← phiReal_eq_phi μ K' L, ← Function.comp_apply (f := phiReal μ K K')]
    rw [phiReal_comp_of_isValExtension' μ K K' L u]
  apply_mod_cast this
