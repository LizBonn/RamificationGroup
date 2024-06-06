import RamificationGroup.LowerNumbering
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.GroupTheory.Index
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Algebra.Group.Basic

open DiscreteValuation Subgroup Set Function Finset BigOperators Int Valued

theorem ceil_nonpos {u : ℚ} (h : u ≤ 0) : ⌈u⌉ ≤ 0 := by
  by_contra h
  push_neg at *
  have : ¬u ≤ 0 := by linarith [ceil_pos.1 h]
  contradiction

namespace HerbrandFunction

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [Algebra R S]

-- by definition of relindex, it's always 1 when u < 0
noncomputable def phiDeriv (u : ℚ) : ℚ :=
  1 / (relindex G(S/R)_[(⌈u⌉)] G(S/R)_[0])

noncomputable def phi (u : ℚ) : ℚ :=
  ∑ x in Finset.Icc 1 (⌈u⌉ - 1), (phiDeriv R S x) + (u - (max 0 (⌈u⌉ - 1))) * (phiDeriv R S u)

theorem phiDeriv_eq_one_of_le_zero {u : ℚ} (hu : u ≤ 0) : phiDeriv R S u = 1 := by
  unfold phiDeriv relindex
  simp
  apply lowerRamificationGroup.antitone
  apply ceil_nonpos hu

theorem phi_eq_self_of_le_zero {u : ℚ} (hu : u ≤ 0) : phi R S u = u := by
  unfold phi
  simp [phiDeriv_eq_one_of_le_zero R S hu]
  have h : ⌈u⌉ - 1 ≤ 0 := by linarith [ceil_nonpos hu]
  have h' : ⌈u⌉ - 1 < 1 := by linarith [h]
  calc
    _ = (u - max 0 (⌈u⌉ - 1)) := by simp [h']
    _ = u := by simp [h]

theorem phiDeriv_pos (u : ℚ) : 0 < phiDeriv R S u := by
  unfold phiDeriv relindex index
  apply one_div_pos.2
  have h : 0 < (Nat.card (↥ G(S/R)_[0] ⧸ subgroupOf G(S/R)_[⌈u⌉] G(S/R)_[0])) := by
    apply Nat.card_pos_iff.2 ⟨sorry, sorry⟩
  exact_mod_cast h

theorem phiDeriv_eq_ceil {u : ℚ} : phiDeriv R S u = phiDeriv R S ⌈u⌉ := by
  unfold phiDeriv
  simp

theorem phi_pos_of_pos {u : ℚ} (hu : 0 < u) : 0 < phi R S u := by
  unfold phi
  have h : 0 ≤ ∑ x in Finset.Icc 1 (⌈u⌉ - 1), phiDeriv R S x := by
    --apply sum_pos
    sorry
  have h' : 0 < (u - (max 0 (⌈u⌉ - 1))) * phiDeriv R S u := by
    apply mul_pos
    simp [hu]
    linarith [ceil_lt_add_one u]
    exact phiDeriv_pos R S u
  linarith [h, h']

theorem phi_pos_gt_nonpos {a b : ℚ} (hu1 : a ≤ 0) (hu2 : 0 < b) : phi R S a < phi R S b := by
  apply lt_of_le_of_lt (b := 0)
  rw [phi_eq_self_of_le_zero]
  <;> exact hu1
  exact phi_pos_of_pos R S hu2

theorem phi_of_pos_of_le_one {u : ℚ} (h1 : 0 < u) (h2 : u ≤ 1) : phi R S u = u * phiDeriv R S u := by
  unfold phi
  have huc : ⌈u⌉ = 1 := by
    apply ceil_eq_iff.2
    simp [h1, h2]
  have huf1 : ⌈u⌉ - 1 < 1 := by linarith [huc]
  have huf0 : ⌈u⌉ - 1 = 0 := by simp [huc]
  simp [huf1, huf0]

#check Finset.sum_range_sub_sum_range

theorem Finset.sum_Icc_sub_sum_Icc {n : ℤ} {m : ℤ} (hnm : n ≤ m) : ∑ x in Finset.Icc 1 m, phiDeriv R S x - ∑ x in Finset.Icc 1 n, phiDeriv R S x = ∑ x in Finset.Icc (n + 1) m, phiDeriv R S x := by sorry

theorem phi_strictMono_of_gt_one {a b : ℚ} (hb : 1 < b) (hab : a < b) : phi R S a < phi R S b := by
  unfold phi
  by_cases hceil : ⌈a⌉ = ⌈b⌉
  · simp [phiDeriv_eq_ceil, hceil]
    apply (mul_lt_mul_right (by apply phiDeriv_pos R S)).2
    simp [hab]
  · calc
      _ ≤ ∑ x in Finset.Icc 1 ⌈a⌉, phiDeriv R S x := by
        apply le_trans (b := ∑x in Finset.Icc 1 (⌈a⌉ - 1), phiDeriv R S ↑x + 1 * phiDeriv R S ⌈a⌉)
        rw [phiDeriv_eq_ceil R S]
        apply add_le_add_left
        apply (mul_le_mul_right (by apply phiDeriv_pos R S)).2
        have : a - 1 ≤ (max 0 (⌈a⌉ - 1)) := by
          simp
          right; apply le_ceil
        linarith [this]
        have h : ∑ x in Finset.Icc 1 (⌈a⌉ - 1), phiDeriv R S ↑x + 1 * phiDeriv R S ↑⌈a⌉ = ∑ x in Finset.Icc 1 ⌈a⌉, phiDeriv R S ↑x := by sorry
        apply le_of_eq h
      _ ≤ ∑ x in Finset.Icc 1 (⌈b⌉ - 1), phiDeriv R S x := by
        have h : ⌈a⌉ ≤ ⌈b⌉ - 1 := by
          have hc : ⌈a⌉ < ⌈b⌉ := by
            apply lt_of_le_of_ne
            apply ceil_le_ceil
            linarith [hab]
            push_neg at hceil
            exact hceil
          apply le_sub_one_of_lt hc
        have h' : Finset.Icc 1 (⌈a⌉) ⊆ Finset.Icc 1 (⌈b⌉ - 1) := by apply Finset.Icc_subset_Icc (by linarith) h
        sorry
        --apply sum_le_sum_of_subset h' (f := phiDeriv R S)
      _ < phi R S b := by
        unfold phi
        simp
        apply mul_pos
        simp
        constructor
        · linarith [hb]
        · linarith [ceil_lt_add_one b]
        apply phiDeriv_pos R S

theorem phi_strictMono : StrictMono (phi R S) := by
  rintro a b h
  by_cases ha0 : a ≤ 0
  · by_cases hb0 : b ≤ 0
    · rw [phi_eq_self_of_le_zero R S ha0, phi_eq_self_of_le_zero R S hb0]; assumption
    · by_cases hb1 : b ≤ 1
      · push_neg at *
        apply phi_pos_gt_nonpos R S ha0 hb0
      · push_neg at *
        apply phi_pos_gt_nonpos R S ha0 hb0
  · by_cases ha1 : a ≤ 1
    push_neg at *
    have hac : ⌈a⌉ = 1 := by
      apply ceil_eq_iff.2
      simp [ha0, ha1]
    · by_cases hb1 : b ≤ 1
      · push_neg at *
        have hbc : ⌈b⌉ = 1 := by
          apply ceil_eq_iff.2
          simp [lt_trans ha0 h, hb1]
        have hceil : ⌈a⌉ = ⌈b⌉ := by simp [hac, hbc]
        have hderiv : phiDeriv R S a = phiDeriv R S b := by
          unfold phiDeriv
          simp [hceil]
        rw [phi_of_pos_of_le_one R S ha0 ha1, phi_of_pos_of_le_one R S (by linarith) hb1]
        simp [hderiv]
        apply (mul_lt_mul_right (by apply phiDeriv_pos R S)).2 h
      · apply phi_strictMono_of_gt_one R S (by linarith) h
    apply phi_strictMono_of_gt_one R S (by linarith) h


--i don't know
theorem exist_aux (y : ℚ) : ∃ n , phi R S (n - 1) ≤ y ∧ y < phi R S n := by sorry


theorem phi_Bijective : Function.Bijective (phi R S) := by
  constructor
  · rintro a1 a2 h
    contrapose! h
    by_cases h1 : a1 > a2
    · apply ne_of_gt (phi_strictMono R S h1)
    · push_neg at *
      apply ne_of_lt (phi_strictMono R S (lt_of_le_of_ne h1 h))
  · rintro y
    obtain ⟨n, ⟨hn, hn'⟩⟩  := exist_aux R S y
    use (y - phi R S (n - 1)) * (relindex G(S/R)_[⌈n⌉] G(S/R)_[0]) + n - 1
    unfold phi
    sorry


noncomputable def psi : ℚ → ℚ :=
  invFun (phi R S)

theorem psi_bij : Function.Bijective (psi R S) := by
  constructor
  have hpsi: (invFun (phi R S)).Injective :=
    (rightInverse_invFun (phi_Bijective R S).2).injective
  exact hpsi
  apply invFun_surjective
  apply (phi_Bijective R S).1

theorem phi_zero_eq_zero : phi R S 0 = 0 := by
  unfold phi
  simp

noncomputable def psi' (v : ℚ): ℚ :=
  1 / (phiDeriv R S (psi R S v))

  theorem psi_zero_eq_zero : psi R S 0 = 0 := by
  unfold psi
  nth_rw 1 [← phi_zero_eq_zero R S]
  have : id 0 = (0 : ℚ) := by rfl
  nth_rw 2 [← this]
  have Inj : (phi R S).Injective := by apply (phi_Bijective R S).1
  rw [← invFun_comp Inj]
  simp

theorem leftInverse_phi_psi : Function.LeftInverse (phi R S) (psi R S)  := by
  rintro a
  apply invFun_eq
  apply (phi_Bijective R S).surjective

@[simp]
theorem phi_psi_eq_self (u : ℚ) : (phi R S) ((psi R S) u) = u := leftInverse_phi_psi R S u


theorem psi_eq_self_of_le_neg_one {v : ℚ} (hv : v ≤ 0) : psi R S v = v := by
  have h1 : phi R S (psi R S v) = v := by apply phi_psi_eq_self
  have h2 : phi R S v = v := by apply phi_eq_self_of_le_zero R S hv
  apply (phi_Bijective R S).injective
  simp [h1, h2]

--lemma 3
open scoped Classical


variable (K L : Type*) {ΓK : outParam Type*} [Field K] [Field L] [LinearOrderedCommGroupWithZero ΓK] [vK : Valued K ΓK] [vS : Valued L ℤₘ₀] [Algebra K L] [FiniteDimensional K L]

noncomputable def G_diff (i : ℤ) : Finset (L ≃ₐ[K] L) := ((G(L/K)_[i] : Set (L ≃ₐ[K] L)) \ (G(L/K)_[(i + 1)] : Set (L ≃ₐ[K] L))).toFinset
noncomputable def Ramification_Group_diff (i : ℤ) : Finset (L ≃ₐ[K] L) := ((G(L/K)_[i] : Set (L ≃ₐ[K] L)) \ (G(L/K)_[(i + 1)] : Set (L ≃ₐ[K] L))).toFinset

theorem G_pairwiseDisjoint (n : ℤ) : (PairwiseDisjoint (↑(Finset.Icc (-1) (n - 1))) (G_diff K L)) := by
  induction' n with n ih
  induction' n with n ih
  simp
  sorry
  sorry

theorem Ramification_Group_pairwiseDisjoint (n : ℤ) : (PairwiseDisjoint (↑(Finset.Icc (-1) (n - 1))) (Ramification_Group_diff K L)) := by
  sorry

--i don't know how to name them
theorem x_in_G_n {x : (L ≃ₐ[K] L)} (hx : x ≠ .refl): ∃ (n : ℤ) , -1 ≤ n ∧ x ∈ G(L/K)_[n] ∧ x ∉ G(L/K)_[(n + 1)] := by
  by_contra hc
  push_neg at *
  sorry


theorem mem_all_lowerRamificationGroup_iff {x : (L ≃ₐ[K] L)}: (∀ n : ℤ, x ∈ G(L/K)_[n]) ↔ x = .refl := by
  constructor
  <;>rintro h
  have htop : i_[L/K] x = ⊤ := by
    by_contra hc
    simp at hc
    push_neg at *
    obtain ⟨m, hx, hx', hx''⟩ := x_in_G_n K L hc
    apply hx''
    apply h
  apply lowerIndex_eq_top_iff_eq_refl.1 htop
  rintro n
  have : x ∈ G(L/K)_[n.toNat] := by
    apply (mem_lowerRamificationGroup_iff n.toNat).2
    rw [h, (lowerIndex_refl (R := K) (S := L))]
    simp
  sorry



theorem m_lt_n_of_in_G_m_of_notin_G_n {x : (L ≃ₐ[K] L)} {m n : ℤ} (hm : x ∈ G(L/K)_[m]) (hn : x ∉ G(L/K)_[n]) : m ≤ n - 1 := by
  by_contra hc
  push_neg at *
  have h : G(L/K)_[m] ≤  G(L/K)_[n] := by
    convert lowerRamificationGroup.antitone K L hc
    simp
  sorry

theorem G_n_or_G_lt_n {n : ℤ} {x : (L ≃ₐ[K] L)} (h : x ∉ G(L/K)_[n]) : ∃ a, (-1 ≤ a ∧ a ≤ n - 1) ∧ x ∈ G_diff K L a := by
  have hx : x ≠ .refl := by
    by_contra hc
    have : x ∈ G(L/K)_[n] := by apply (mem_all_lowerRamificationGroup_iff K L).2 hc
    contradiction
  obtain ⟨m, ⟨hmgt, hx, hx'⟩⟩ := (x_in_G_n K L hx)
  have hm' : m ≤ n - 1 := by apply m_lt_n_of_in_G_m_of_notin_G_n K L hx h
  have hx'' : x ∈ G_diff K L m := by simp [G_diff, hx, hx']
  use m

theorem Raimification_Group_split (n : ℤ) : (⊤ : Finset (L ≃ₐ[K] L)) = (disjiUnion (Finset.Icc (-1) (n - 1)) (Ramification_Group_diff K L) (G_pairwiseDisjoint K L n)) ∪ (G(L/K)_[n] : Set (L ≃ₐ[K] L)).toFinset := by
  ext x
  constructor
  simp
  by_cases h : x ∈ G(L/K)_[n]
  · right
    assumption
  left
  apply G_n_or_G_lt_n K L h
  simp

-- theorem Sum_Trunc_lower_Index_of_G_n (n : ℤ) (u : ℚ) (h : u ≤ n) : (Finset.sum (G(L/K)_[n] : Set (L ≃ₐ[K] L)).toFinset ((AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) = (u + 1) * (Nat.card (G(L/K)_[n])) := by
--   calc
--   _ = Finset.sum (G(L/K)_[n] : Set (L ≃ₐ[K] L)).toFinset (fun (x : _) => u + 1) := by
--     apply sum_equiv (.refl (L ≃ₐ[K] L))
--     simp
--     rintro s hs
--     sorry
--   _ = (u + 1) * (Nat.card (G(L/K)_[n])) := by
--     norm_num
--     ring

-- theorem Sum_Trunc_lower_Index_of_diff_G (n : ℤ) (u : ℚ) (h : n ≤ u) : (Finset.sum (G_diff K L n) ((AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) = (n + 1) * (Nat.card (G_diff K L n)) := by
--   calc
--   _ = (Finset.sum (G_diff K L n) (fun (x : _) => ((n : ℚ) + 1))) := by
--     apply sum_equiv (.refl (L ≃ₐ[K] L))
--     simp
--     rintro s hs
--     sorry
--   _ = (n + 1) * (Nat.card (G_diff K L n)) := by
--     norm_num
--     ring

theorem relindex_aux {u : ℚ} : relindex G(L/K)_[⌈u⌉] G(L/K)_[0] = (Nat.card G(L/K)_[0]) / Nat.card G(L/K)_[⌈u⌉] := by sorry

theorem phi_eq_sum_card {u : ℚ} : phi K L u = (1 / Nat.card G(L/K)_[0]) * ((∑ x in Finset.Icc 1 (⌈u⌉ - 1), Nat.card G(L/K)_[x]) + (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈u⌉])) := by
  unfold phi phiDeriv
  calc
    _ = ∑ x in Finset.Icc 1 (⌈u⌉ - 1), (1 / Nat.card G(L/K)_[0]) * (Nat.card G(L/K)_[x]) + (u - ↑(max 0 (⌈u⌉ - 1))) * (1 / ↑(relindex G(L/K)_[⌈u⌉] G(L/K)_[0])) := by sorry
    _ = (1 / Nat.card G(L/K)_[0]) * (∑ x in Finset.Icc 1 (⌈u⌉ - 1), Nat.card G(L/K)_[x]) + (u - (max 0 (⌈u⌉ - 1))) * (1 / ↑(relindex G(L/K)_[⌈u⌉] G(L/K)_[0])) := by
      rw [(Finset.mul_sum (Finset.Icc 1 (⌈u⌉ - 1)) (fun i => Nat.card (lowerRamificationGroup K L i)) (1 / Nat.card G(L/K)_[0])).symm]
      simp
      sorry
    _ = (1 / Nat.card G(L/K)_[0]) * ((∑ x in Finset.Icc 1 (⌈u⌉ - 1), Nat.card G(L/K)_[x]) + (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈u⌉])) := by
      simp [relindex_aux, mul_add]
      sorry

theorem insert_Icc {u : ℚ} : Finset.Icc 0 (⌈u⌉ - 1) = insert 0 (Finset.Icc 1 (⌈u⌉ - 1)) := by sorry

theorem sum_insert_aux {u : ℚ} : (∑ x in Finset.Icc 0 (⌈u⌉ - 1), Nat.card G(L/K)_[x]) - Nat.card G(L/K)_[0] = (∑ x in Finset.Icc 1 (⌈u⌉ - 1), Nat.card G(L/K)_[x]):= by
  calc
    _ = (∑ x in insert 0 (Finset.Icc 1 (⌈u⌉ - 1)), Nat.card G(L/K)_[x] - Nat.card G(L/K)_[0]) := by
      rw [insert_Icc]
    _ = (∑ x in Finset.Icc 1 (⌈u⌉ - 1), Nat.card G(L/K)_[x]) := by simp

theorem sum_sub_aux {u : ℚ} : (∑ i in Finset.Icc (-1) (⌈u⌉ - 1), (i + 1) * (Nat.card G(L/K)_[i] - Nat.card G(L/K)_[(i + 1)])) = ∑ i in Finset.Icc 0 (⌈u⌉ - 1), Nat.card G(L/K)_[i] - ⌈u⌉ * (Nat.card G(L/K)_[⌈u⌉]) := by sorry

theorem sum_of_diff_aux {i : ℤ} {u : ℚ} : ∀ i ∈ Finset.Icc 0 (⌈u⌉ - 1), (i + 1) * (Nat.card G(L/K)_[i] - Nat.card G(L/K)_[(i + 1)]) = ∑ s in Ramification_Group_diff K L i, (AlgEquiv.truncatedLowerIndex K L (u + 1) s) := by sorry

theorem sum_fiberwise_aux {u : ℚ} : ((Finset.sum (⊤ : Finset (L ≃ₐ[K] L)) (AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) = ∑ i in Finset.Icc (-1) (⌈u⌉ - 1), ∑ s in Ramification_Group_diff K L i, (AlgEquiv.truncatedLowerIndex K L (u + 1) s) + (u + 1) * (Nat.card ↥ G(L/K)_[⌈u⌉]) := by
  rw [Raimification_Group_split K L ⌈u⌉, sum_union, sum_disjiUnion]
  congr 1
  calc
    _ =  ∑ x in (G(L/K)_[⌈u⌉] : Set (L ≃ₐ[K] L)).toFinset , u + 1 := by sorry
    _ = (u + 1) * (Nat.card G(L/K)_[⌈u⌉]) := by sorry
  sorry


#check Finset.sum_disjiUnion
#check Set.union_diff_cancel
#check Finset.sum_fiberwise
#check (mul_one_div ((Nat.card G(L/K)_[0]) : ℚ) ((Nat.card G(L/K)_[0]) : ℚ))



theorem phi_eq_sum_inf (u : ℚ) : (phi K L u) = (1 / Nat.card G(L/K)_[0]) * ((Finset.sum (⊤ : Finset (L ≃ₐ[K] L)) (AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) - 1 := by
  by_cases hu : u ≤ 0
  · sorry
  · have hu' : 0 ≤ ⌈u⌉ - 1 := by sorry
    calc
      _ = (1 / Nat.card G(L/K)_[0]) * ((∑ x in Finset.Icc 1 (⌈u⌉ - 1), Nat.card G(L/K)_[x]) + (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈u⌉])) := by
        apply phi_eq_sum_card K L
      _ = (1 / Nat.card G(L/K)_[0]) * ((∑ x in Finset.Icc 0 (⌈u⌉ - 1), Nat.card G(L/K)_[x]) + (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈u⌉])) - (1 : ℕ) := by
        have h : 0 < Nat.card G(L/K)_[0] := by sorry
        rw [← sum_insert_aux, ← (Nat.div_self h)]
        sorry
      _ = (1 / Nat.card G(L/K)_[0]) * ((∑ i in Finset.Icc (-1) (⌈u⌉ - 1), (i + 1) * (Nat.card G(L/K)_[i] - Nat.card G(L/K)_[(i + 1)])) + (u + 1) * (Nat.card G(L/K)_[⌈u⌉])) - 1 := by
        rw [sum_sub_aux]
        simp
        have h : (u - max 0 (⌈u⌉ - 1)) * (Fintype.card G(L/K)_[⌈u⌉] ) = (u + 1) * (Fintype.card ↥ G(L/K)_[⌈u⌉]) - ⌈u⌉ * (Fintype.card G(L/K)_[⌈u⌉] ) := by
          simp [hu', ← sub_add]
          ring
        sorry
      _ = (1 / Nat.card G(L/K)_[0]) * ((∑ i in Finset.Icc (-1) (⌈u⌉ - 1), ∑ s in Ramification_Group_diff K L i, (AlgEquiv.truncatedLowerIndex K L (u + 1) s)) + (u + 1) * (Nat.card G(L/K)_[⌈u⌉])) - 1 := by
        congr 3
        have h : Finset.Icc (-1) (⌈u⌉ - 1) = Finset.Icc (-1) (⌈u⌉ - 1) := by rfl
        sorry
        --apply sum_congr h (sum_of_diff_aux K L)
      _ = (1 / Nat.card G(L/K)_[0]) * ((Finset.sum (⊤ : Finset (L ≃ₐ[K] L)) (AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) - 1 := by
        congr 2
        apply (sum_fiberwise_aux K L (u := u)).symm


  -- by_cases h : u ≥ 1
  -- · simp [h]
  --   have hsplit : (Finset.sum (⊤ : Finset (L ≃ₐ[K] L)) (AlgEquiv.truncatedLowerIndex K L (u + 1) ·)) = (Finset.sum (((disjiUnion (Finset.Icc (-1) (⌈u⌉ - 1)) (G_diff K L) (G_pairwiseDisjoint K L _)))) ((AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) + (Finset.sum (((G(L/K)_[(⌈u⌉)] : Set (L ≃ₐ[K] L)).toFinset)) ((AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) := by
  --     calc
  --     _ = (Finset.sum (((disjiUnion (Finset.Icc (-1) (⌈u⌉ - 1)) (G_diff K L) (G_pairwiseDisjoint K L _)) ∪ (G(L/K)_[(⌈u⌉)] : Set (L ≃ₐ[K] L)).toFinset)) ((AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) := by
  --       congr
  --       apply G_split
  --     _ = (Finset.sum (((disjiUnion (Finset.Icc (-1) (⌈u⌉ - 1)) (G_diff K L) (G_pairwiseDisjoint K L _)))) ((AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) + (Finset.sum (((G(L/K)_[(⌈u⌉)] : Set (L ≃ₐ[K] L)).toFinset)) ((AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) := by
  --       have : Disjoint (disjiUnion (Finset.Icc (-1) (⌈u⌉ - 1)) (G_diff K L) (G_pairwiseDisjoint K L _)) (toFinset ↑ G(L/K)_[⌈u⌉]) := by sorry
  --       apply sum_union
  --       apply this
  --   have hsplit' : (Finset.sum (((disjiUnion (Finset.Icc (-1) (⌈u⌉ - 1)) (G_diff K L) (G_pairwiseDisjoint K L _)))) ((AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) = Finset.sum _ fun (i : ℤ) => Finset.sum _ fun (x : _) => (AlgEquiv.truncatedLowerIndex K L (u + 1) x) := by
  --     apply sum_disjiUnion
  --   simp at hsplit hsplit'
  --   rw [hsplit, hsplit']
  --   have hu : (Finset.sum ((G(L/K)_[(⌈u⌉)] : Set (L ≃ₐ[K] L)).toFinset) ((AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) = (u + 1) * (Nat.card G(L/K)_[⌈u⌉]) := by
  --     convert Sum_Trunc_lower_Index_of_G_n K L ⌈u⌉ u (by apply le_ceil)
  --   rw [hu]
  --   have hd : Finset.sum (Finset.Icc (-1) (⌈u⌉ - 1)) (fun (i : ℤ) => Finset.sum (G_diff K L i) (fun (x : _) => (AlgEquiv.truncatedLowerIndex K L (u + 1) x))) = Finset.sum (Finset.Icc (-1) (⌈u⌉ - 1)) fun (i : ℤ) => (i + 1) * (Nat.card ((G(L/K)_[i] : Set (L ≃ₐ[K] L)) \ G(L/K)_[(i + 1)] : Set (L ≃ₐ[K] L))):= by
  --     norm_num
  --     apply sum_equiv (.refl ℤ)
  --     simp
  --     simp
  --     rintro i hge hle
  --     have hle' : i ≤ u := by
  --       sorry
  --     convert Sum_Trunc_lower_Index_of_diff_G K L i u hle'
  --     unfold G_diff
  --     simp
  --     sorry
  --   rw [hd]
  --   sorry
  -- unfold phi
  -- simp [h]
  -- sorry


variable (S' : Type*) [Ring S'] [vS' : Valued S' ℤₘ₀] [Algebra R S']
theorem phi_eq_ofEquiv {f : S ≃ₐ[R] S'} (hf : ∀ a : S, v a = v (f a)) (u : ℚ) : phi R S u = phi R S' u := sorry

theorem psi_eq_ofEquiv {f : S ≃ₐ[R] S'} (hf : ∀ a : S, v a = v (f a)) (u : ℚ) : psi R S u = psi R S' u := sorry

end HerbrandFunction
