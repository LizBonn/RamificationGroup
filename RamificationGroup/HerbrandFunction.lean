import RamificationGroup.LowerNumbering
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.GroupTheory.Index
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Int.Cast.Basic

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
    by_cases h : ⌈u⌉ - 1 = 0
    · simp [h]
    · apply le_of_lt
      apply sum_pos (s := Finset.Icc 1 (⌈u⌉ - 1))
      · intro i _
        apply phiDeriv_pos
      · simp
        apply Int.le_of_sub_one_lt
        simp [one_le_ceil_iff.2]
        apply lt_of_le_of_ne
        apply one_le_ceil_iff.2 hu
        omega
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
        have h : ∑ x in Finset.Icc 1 (⌈a⌉ - 1), phiDeriv R S ↑x + 1 * phiDeriv R S ↑⌈a⌉ = ∑ x in Finset.Icc 1 ⌈a⌉, phiDeriv R S ↑x := by sorry -- i have done this later
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
        --apply sum_le_sum_of_subset h' --(f := phiDeriv R S)
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


theorem phi_inf (y : ℚ) : ∃ (n : ℕ) , ¬ phi R S n ≤ y := by sorry

--i don't know
--the proof is not good
theorem exist_aux (y : ℚ) : ∃ (n : ℕ) , phi R S (n - 1) ≤ y ∧ y < phi R S n := by
  by_contra h
  push_neg at h
  obtain ⟨n, hn⟩ := phi_inf R S y
  apply hn
  apply h
  sorry

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
    use (y - phi R S (n - 1)) * (relindex G(S/R)_[n] G(S/R)_[0]) + n - 1
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

theorem Ramification_Group_Disjoint {i j : ℤ} {s : (L ≃ₐ[K] L)} (hi : s ∈ Ramification_Group_diff K L i) (hj : s ∈ Ramification_Group_diff K L j) (hij : i ≠ j) : s ∈ (⊥ : Finset (L ≃ₐ[K] L)) := by
  simp
  unfold Ramification_Group_diff at *
  simp at hi hj
  rcases hi with ⟨hi1, hi2⟩
  rcases hj with ⟨hj1, hj2⟩
  by_cases h : i < j
  · have hle : i + 1 ≤ j := by apply Int.le_of_sub_one_lt (by simp [h])
    have hle' : G(L/K)_[j] ≤ G(L/K)_[(i + 1)] := by apply lowerRamificationGroup.antitone K L hle
    apply hi2
    apply mem_of_subset_of_mem hle' hj1
  · have hle : j + 1 ≤ i := by
      apply Int.le_of_sub_one_lt
      apply lt_of_le_of_ne (by push_neg at h; linarith [h]) (by ring; apply hij.symm)
    have hle' : G(L/K)_[i] ≤ G(L/K)_[(j + 1)] := by apply lowerRamificationGroup.antitone K L hle
    apply hj2
    apply mem_of_subset_of_mem hle' hi1

theorem Ramification_Group_pairwiseDisjoint (n : ℤ) : (PairwiseDisjoint (↑(Finset.Icc (-1) (n - 1))) (Ramification_Group_diff K L)) := by
  rintro i _ j _ hij u hu1 hu2
  have hu : u ≤ (Ramification_Group_diff K L i) ∩ (Ramification_Group_diff K L j) := by
    rintro s hs
    simp
    constructor
    · apply mem_of_subset_of_mem hu1 hs
    · apply mem_of_subset_of_mem hu2 hs
  apply le_trans hu
  rintro s hs
  simp at hs
  apply Ramification_Group_Disjoint K L hs.1 hs.2 hij

--i don't know how to name them
theorem x_not_in_aux {x : (L ≃ₐ[K] L)} (hx : x ≠ .refl) : ∃ (n : ℤ) , x ∉ G(L/K)_[n] := by sorry


theorem x_in_G_n {x : (L ≃ₐ[K] L)} (hx : x ≠ .refl) : ∃ (n : ℤ) , -1 ≤ n ∧ x ∈ G(L/K)_[n] ∧ x ∉ G(L/K)_[(n + 1)] := by
  by_contra hc
  push_neg at *
  obtain ⟨n, hn⟩ := x_not_in_aux K L hx
  apply hn
  sorry

theorem mem_all_lowerRamificationGroup_iff {x : (L ≃ₐ[K] L)}: (∀ n : ℤ, x ∈ G(L/K)_[n]) ↔ x = .refl := by
  constructor
  <;>rintro h
  have htop : i_[L/K] x = ⊤ := by
    by_contra hc
    simp at hc
    push_neg at *
    obtain ⟨m, hx, hx', hx''⟩ := x_in_G_n K L sorry -- hc
    apply hx''
    apply h
  sorry
  sorry
  -- apply lowerIndex_eq_top_iff_eq_refl.1 htop
  -- rintro n
  -- have : x ∈ G(L/K)_[n.toNat] := by
  --   apply (mem_lowerRamificationGroup_iff n.toNat).2
  --   rw [h, (lowerIndex_refl (R := K) (S := L))]
  --   simp
  -- sorry

theorem m_lt_n_of_in_G_m_of_notin_G_n {x : (L ≃ₐ[K] L)} {m n : ℤ} (hm : x ∈ G(L/K)_[m]) (hn : x ∉ G(L/K)_[n]) : m ≤ n - 1 := by
  by_contra hc
  push_neg at *
  have h : G(L/K)_[m] ≤  G(L/K)_[n] := by
    convert lowerRamificationGroup.antitone K L hc
    simp
  apply hn
  apply Set.mem_of_subset_of_mem h hm

theorem G_n_or_G_lt_n {n : ℤ} {x : (L ≃ₐ[K] L)} (h : x ∉ G(L/K)_[n]) : ∃ a, (-1 ≤ a ∧ a ≤ n - 1) ∧ x ∈ G_diff K L a := by
  have hx : x ≠ .refl := by
    by_contra hc
    have : x ∈ G(L/K)_[n] := by apply (mem_all_lowerRamificationGroup_iff K L).2 hc
    contradiction
  obtain ⟨m, ⟨hmgt, hx, hx'⟩⟩ := (x_in_G_n K L hx)
  have hm' : m ≤ n - 1 := by apply m_lt_n_of_in_G_m_of_notin_G_n K L hx h
  have hx'' : x ∈ G_diff K L m := by simp [G_diff, hx, hx']
  use m

theorem Raimification_Group_split (n : ℤ) : (⊤ : Finset (L ≃ₐ[K] L)) = (disjiUnion (Finset.Icc (-1) (n - 1)) (Ramification_Group_diff K L) (Ramification_Group_pairwiseDisjoint K L n)) ∪ (G(L/K)_[n] : Set (L ≃ₐ[K] L)).toFinset := by
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
    _ = ∑ x in Finset.Icc 1 (⌈u⌉ - 1), ((1 : ℚ) / Nat.card G(L/K)_[0]) * (Nat.card G(L/K)_[x]) + (u - (max 0 (⌈u⌉ - 1))) * (1 / (relindex G(L/K)_[⌈u⌉] G(L/K)_[0])) := by
      congr
      ext x
      rw [relindex_aux, div_mul_eq_mul_div, one_mul, Nat.cast_div, one_div_div]
      simp
      · simp
        apply Subgroup.card_dvd_of_le
        apply lowerRamificationGroup.antitone
        sorry
      · sorry
    _ = ((1 : ℚ) / Nat.card G(L/K)_[0]) * (∑ x in Finset.Icc 1 (⌈u⌉ - 1), Nat.card G(L/K)_[x]) + (u - (max 0 (⌈u⌉ - 1))) * (1 / ↑(relindex G(L/K)_[⌈u⌉] G(L/K)_[0])) := by
      rw [(Finset.mul_sum (Finset.Icc 1 (⌈u⌉ - 1)) (fun i => (Nat.card (lowerRamificationGroup K L i) : ℚ)) ((1 : ℚ) / Nat.card G(L/K)_[0])).symm]
      simp
    _ = (1 / Nat.card G(L/K)_[0]) * ((∑ x in Finset.Icc 1 (⌈u⌉ - 1), Nat.card G(L/K)_[x]) + (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈u⌉])) := by
      simp [relindex_aux, mul_add]
      rw [Nat.cast_div, inv_div, div_eq_mul_inv]
      ring
      sorry; sorry

theorem insert_Icc_left (a b : ℤ) (ha : a ≤ b): Finset.Icc a b = insert a (Finset.Icc (a + 1) b) := by
  ext x
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 h
    rw [Finset.insert_eq]
    apply Finset.mem_union.2
    by_cases h : x = a
    · left
      simp [h]
    · right
      push_neg at *
      apply Finset.mem_Icc.2
      constructor
      · apply Int.le_of_sub_one_lt
        simp [lt_of_le_of_ne h1 h.symm]
      exact h2
  · rw [Finset.insert_eq, Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
    rintro h
    rcases h with h | ⟨h1, h2⟩
    · constructor
      · apply le_of_eq (Finset.mem_singleton.1 h).symm
      · apply le_trans (le_of_eq (Finset.mem_singleton.1 h)) ha
    · constructor
      · linarith [h1]
      · exact h2

theorem insert_Icc_right (a b : ℤ) (h : a ≤ b) : Finset.Icc a b = insert b (Finset.Icc a (b - 1)) := by
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.insert_eq b (Finset.Icc a (b - 1))]
    apply Finset.mem_union.2
    by_cases h : x = b
    · left
      simp [h]
    · right
      simp at hx
      simp
      constructor
      · exact hx.1
      · apply Int.le_of_sub_one_lt
        apply lt_of_le_of_ne
        linarith
        push_neg at h
        simp [h]
  · rw [Finset.insert_eq b (Finset.Icc a (b - 1))]
    apply Finset.union_subset
    simp [h]
    apply Finset.Icc_subset_Icc
    rfl; linarith

theorem sum_insert_left_aux (a b : ℤ) (ha : a ≤ b) (f : ℤ → ℕ) : (∑ x in Finset.Icc a b, f x) - f a = (∑ x in Finset.Icc (a + 1) b, f x):= by
  calc
    _ = ∑ x in insert a (Finset.Icc (a + 1) b), f x - f a := by
      rw [insert_Icc_left _ _ ha]
    _ = (∑ x in Finset.Icc (a + 1) b, f x) := by simp

theorem sum_insert_left_aux' (a b : ℤ) (h : a ≤ b) (f : ℤ → ℤ) : (∑ x in Finset.Icc a b, f x) - f a = (∑ x in Finset.Icc (a + 1) b, f x) := by
  calc
    _ = ∑ x in insert a (Finset.Icc (a + 1) b), f x - f a := by
      rw [insert_Icc_left _ _ h]
    _ = (∑ x in Finset.Icc (a + 1) b, f x) := by simp

theorem sum_insert_right_aux' (a b : ℤ) (h : a ≤ b) (f : ℤ → ℤ) : (∑ x in Finset.Icc a b, f x) = (∑ x in Finset.Icc a (b - 1), f x) + f b := by
  calc
    _ = ∑ x in insert b (Finset.Icc a (b - 1)), f x := by
      rw [insert_Icc_right _ _ h]
    _ = (∑ x in Finset.Icc a (b - 1), f x) + f b := by simp [add_comm]

#check sum_sub_distrib

theorem sum_sub_aux {u : ℚ} (hu : 0 ≤ ⌈u⌉ - 1): (∑ i in Finset.Icc (-1) (⌈u⌉ - 1), (i + 1) * (Nat.card G(L/K)_[i] - Nat.card G(L/K)_[(i + 1)])) = ∑ i in Finset.Icc 0 (⌈u⌉ - 1), Nat.card G(L/K)_[i] - ⌈u⌉ * (Nat.card G(L/K)_[⌈u⌉]) := by
  calc
    _ = ∑ i in Finset.Icc (-1) (⌈u⌉ - 1), ((i + 1) * Nat.card G(L/K)_[i] - (i + 1) * Nat.card G(L/K)_[(i + 1)]) := by
      apply (Finset.sum_eq_sum_iff_of_le _).2
      · intro i hi
        rw [mul_sub]
      · intro i hi
        apply le_of_eq
        rw [mul_sub]
    _ = ∑ i in Finset.Icc (-1) (⌈u⌉ - 1), (i + 1) * Nat.card G(L/K)_[i] - ∑ i in Finset.Icc (-1) (⌈u⌉ - 1), (i + 1) * Nat.card G(L/K)_[(i + 1)] := by
      rw [sum_sub_distrib]
    _ = ∑ i in Finset.Icc (-1) (⌈u⌉ - 1), (i + 1) * Nat.card G(L/K)_[i] - ∑ i in Finset.Icc 0 ⌈u⌉, i * Nat.card G(L/K)_[i] := by
      congr 1
      let e : ℤ ≃ ℤ :=
      {
        toFun := fun x => x + 1
        invFun := fun x => x - 1
        left_inv := by
          rintro x
          simp
        right_inv := by
          rintro x
          simp
      }
      apply sum_equiv e
      rintro i
      constructor
      · simp
        intro hi1 hi2
        simp [e]
        constructor
        · linarith [hi1]
        · apply add_one_le_ceil_iff.1 (by linarith [hi2])
      · simp
        intro hi
        simp [e] at *
        intro hi'
        constructor
        · linarith [hi]
        · linarith [add_one_le_ceil_iff.2 hi']
      rintro i hi
      simp [e]
    _ = ((-1) + 1) * Nat.card G(L/K)_[(-1)] + ∑ i in Finset.Icc 0 (⌈u⌉ - 1), (i + 1) * Nat.card G(L/K)_[i] - ∑ i in Finset.Icc 0 (⌈u⌉ - 1), i * Nat.card G(L/K)_[i] - ⌈u⌉ * Nat.card G(L/K)_[⌈u⌉] := by
      have h : (-1) ≤ ⌈u⌉ - 1 := by linarith [hu]
      erw [← sum_insert_left_aux' (-1) (⌈u⌉ - 1) h (fun i => (i + 1) * Nat.card (lowerRamificationGroup K L i)), sub_sub, ← sum_insert_right_aux' 0 ⌈u⌉ (by linarith [h]) (fun i => i * Nat.card (lowerRamificationGroup K L i))]
      simp
    _ = ∑ i in Finset.Icc 0 (⌈u⌉ - 1), Nat.card G(L/K)_[i] - ⌈u⌉ * (Nat.card G(L/K)_[⌈u⌉]) := by
      sorry
      -- rw [neg_add_self, zero_mul, zero_add]
      -- congr
      -- rw [← sum_sub_distrib]
      -- ring_nf
      -- simp

theorem truncatedLowerindex_eq_if {i : ℤ} {u : ℚ} {s : (L ≃ₐ[K] L)} (hu : i ≤ (⌈u⌉ - 1)) (hs : s ∈ Ramification_Group_diff K L i) : i_[L/K]ₜ (u + 1) s = i + 1 := by
  unfold Ramification_Group_diff at hs
  simp at hs
  rcases hs with ⟨hs1, hs2⟩
  sorry

theorem sum_of_diff_aux {i : ℤ} {u : ℚ} (h : i ∈ Finset.Icc (-1) (⌈u⌉ - 1)) : ∑ s in Ramification_Group_diff K L i, (AlgEquiv.truncatedLowerIndex K L (u + 1) s) = (i + 1) * (Nat.card G(L/K)_[i] - Nat.card G(L/K)_[(i + 1)]) := by
  calc
     ∑ s in Ramification_Group_diff K L i, (AlgEquiv.truncatedLowerIndex K L (u + 1) s) = ∑ s in Ramification_Group_diff K L i, ((i : ℚ) + 1) := by
      apply sum_equiv (by rfl : (L ≃ₐ[K] L) ≃ (L ≃ₐ[K] L)) (by simp)
      intro s hs
      apply truncatedLowerindex_eq_if
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 h
      exact h2
      exact hs
     _ = (i + 1) * (Nat.card G(L/K)_[i] - Nat.card G(L/K)_[(i + 1)]) := by
      simp [← mul_sum (Ramification_Group_diff K L i) (fun x => 1) (i + 1), add_mul, mul_comm]
      unfold Ramification_Group_diff
      have hsub : (G(L/K)_[(i + 1)] : Set (L ≃ₐ[K] L)) ⊆ (G(L/K)_[i] : Set (L ≃ₐ[K] L)) := by
        apply lowerRamificationGroup.antitone
        linarith
      have h : (((G(L/K)_[i] : Set (L ≃ₐ[K] L)) \ (G(L/K)_[(i + 1)] : Set (L ≃ₐ[K] L))).toFinset).card = ((Fintype.card G(L/K)_[i] ) - (Fintype.card G(L/K)_[(i + 1)])) := by
        rw [toFinset_diff, card_sdiff (by apply Set.toFinset_mono hsub)]
        simp
      rw [h, Nat.cast_sub]
      sorry


--for lower numbering
--the type of lowerindex and the reletive theorems
theorem truncatedLowerindex_eq_of_lt {s : (L ≃ₐ[K] L)} {u : ℚ} (h : s ∈ G(L/K)_[⌈u⌉]) : i_[L/K]ₜ (u + 1) s = u + 1 := by
  unfold AlgEquiv.truncatedLowerIndex
  by_cases ht : i_[L/K] s = ⊤
  · simp [ht]
  · simp [ht]
    have hi : ⌈u⌉.toNat + 1 ≤ i_[L/K] s := by
     sorry
     --apply (mem_lowerRamificationGroup_iff ⌈u⌉.toNat).1
    have hc : u + 1 ≤ ⌈u⌉ + 1 := by sorry
    apply le_trans hc
    sorry

theorem sum_fiberwise_aux {u : ℚ} : ((Finset.sum (⊤ : Finset (L ≃ₐ[K] L)) (AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) = ∑ i in Finset.Icc (-1) (⌈u⌉ - 1), ∑ s in Ramification_Group_diff K L i, (AlgEquiv.truncatedLowerIndex K L (u + 1) s) + (u + 1) * (Nat.card ↥ G(L/K)_[⌈u⌉]) := by
  rw [Raimification_Group_split K L ⌈u⌉, sum_union, sum_disjiUnion]
  congr 1
  calc
    _ =  ∑ x in (G(L/K)_[⌈u⌉] : Set (L ≃ₐ[K] L)).toFinset , (u + 1) := by
      apply sum_equiv (by rfl : (L ≃ₐ[K] L) ≃ (L ≃ₐ[K] L)) (by simp)
      intro i hi
      apply truncatedLowerindex_eq_of_lt
      apply Set.mem_toFinset.1 hi
    _ = (u + 1) * (Nat.card G(L/K)_[⌈u⌉]) := by
      simp [← mul_sum (G(L/K)_[⌈u⌉] : Set (L ≃ₐ[K] L)).toFinset (fun _ => 1) (u + 1), add_mul, mul_comm]
  simp [Finset.disjoint_iff_ne]
  intro s n _ hn2 hs b hb
  unfold Ramification_Group_diff at *
  simp at hs
  rcases hs with ⟨_, hs2⟩
  by_contra h
  have h' : s ∈ G(L/K)_[⌈u⌉] := by
     rw [← h] at hb; exact hb
  have hs : s ∉ G(L/K)_[⌈u⌉] := by
    apply Set.not_mem_subset _ hs2
    apply lowerRamificationGroup.antitone
    linarith [hn2]
  apply hs h'


#check Finset.sum_disjiUnion
#check Set.union_diff_cancel
#check Finset.sum_fiberwise
#check (mul_one_div ((Nat.card G(L/K)_[0]) : ℚ) ((Nat.card G(L/K)_[0]) : ℚ))

theorem cast_natCast (n : ℕ) : ((n : ℤ) : R) = n := by sorry

theorem phi_eq_sum_inf (u : ℚ) : (phi K L u) = (1 / Nat.card G(L/K)_[0]) * ((Finset.sum (⊤ : Finset (L ≃ₐ[K] L)) (AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) - 1 := by
  by_cases hu : u ≤ 0
  · have hu' : ⌈u⌉ - 1 < 0 := by
      apply lt_of_lt_of_le
      linarith [ceil_lt_add_one u]
      apply ceil_le.2 hu
    rw [phi_eq_self_of_le_zero K L hu, sum_fiberwise_aux K L]
    symm
    by_cases huc : ⌈u⌉ < 0
    · have huc' : ⌈u⌉ - 1 < (-1) := by linarith [huc]
      simp [huc', mul_comm, mul_assoc, mul_inv_self]
      sorry
    · have huc' : ⌈u⌉ = 0 := by omega
      have huc'' : ⌈u⌉ - 1 = (-1) := by linarith [huc']
      have hsum : ∑ s in Ramification_Group_diff K L (-1), i_[L/K]ₜ (u + 1) s = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        simp [truncatedLowerindex_eq_if K L (by linarith [huc'']) hx]
      simp [huc', huc'', hsum, mul_comm, mul_assoc, mul_inv_self]
      sorry
  · have hu' : 0 ≤ ⌈u⌉ - 1 := by
      push_neg at hu
      simp [add_one_le_ceil_iff.2 hu, hu]
    calc
      _ = (1 / Nat.card G(L/K)_[0]) * ((∑ i in Finset.Icc 1 (⌈u⌉ - 1), Nat.card G(L/K)_[i]) + (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈u⌉])) := by
        apply phi_eq_sum_card K L
      _ = (1 / Nat.card G(L/K)_[0]) * ((∑ i in Finset.Icc 0 (⌈u⌉ - 1), Nat.card G(L/K)_[i]) + (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈u⌉])) - (1 : ℕ) := by
        have h : 0 < Nat.card G(L/K)_[0] := by sorry
        erw [← sum_insert_left_aux 0 (⌈u⌉ - 1) hu' (fun x => Nat.card (lowerRamificationGroup K L x)), ← (Nat.div_self h), Nat.cast_div (by simp) (by sorry -- simp [h]
        ), ← (mul_one_div ((Nat.card G(L/K)_[0]) : ℚ) ((Nat.card G(L/K)_[0]) : ℚ)), (mul_comm ((Nat.card ↥ G(L/K)_[0]) : ℚ) (1 / ↑(Nat.card ↥ G(L/K)_[0] ))), ← mul_sub, Nat.cast_sub]
        --simp [add_comm, add_sub, add_comm]
        sorry
        sorry
      _ = (1 / Nat.card G(L/K)_[0]) * ((∑ i in Finset.Icc (-1) (⌈u⌉ - 1), (i + 1) * (Nat.card G(L/K)_[i] - Nat.card G(L/K)_[(i + 1)])) + (u + 1) * (Nat.card G(L/K)_[⌈u⌉])) - 1 := by
        rw [sum_sub_aux K L hu', cast_sub]
        congr 2
        have h : (u - max 0 (⌈u⌉ - 1)) * (Nat.card G(L/K)_[⌈u⌉]) = (u + 1) * (Nat.card G(L/K)_[⌈u⌉]) - ⌈u⌉ * (Nat.card G(L/K)_[⌈u⌉]) := by
          simp [hu', ← sub_add]
          ring
        rw [h, add_sub, cast_mul, cast_natCast, add_comm_sub, add_sub]
        congr
      _ = (1 / Nat.card G(L/K)_[0]) * ((∑ i in Finset.Icc (-1) (⌈u⌉ - 1), ∑ s in Ramification_Group_diff K L i, (AlgEquiv.truncatedLowerIndex K L (u + 1) s)) + (u + 1) * (Nat.card G(L/K)_[⌈u⌉])) - 1 := by
        congr 3
        have h : Finset.Icc (-1) (⌈u⌉ - 1) = Finset.Icc (-1) (⌈u⌉ - 1) := by rfl
        rw [Int.cast_sum]
        apply sum_congr h
        intro x hx
        simp [(sum_of_diff_aux K L hx)]
      _ = (1 / Nat.card G(L/K)_[0]) * ((Finset.sum (⊤ : Finset (L ≃ₐ[K] L)) (AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) - 1 := by
        congr 2
        apply (sum_fiberwise_aux K L (u := u)).symm

variable (S' : Type*) [Ring S'] [vS' : Valued S' ℤₘ₀] [Algebra R S']
theorem phi_eq_ofEquiv {f : S ≃ₐ[R] S'} (hf : ∀ a : S, v a = v (f a)) (u : ℚ) : phi R S u = phi R S' u := sorry

theorem psi_eq_ofEquiv {f : S ≃ₐ[R] S'} (hf : ∀ a : S, v a = v (f a)) (u : ℚ) : psi R S u = psi R S' u := sorry
