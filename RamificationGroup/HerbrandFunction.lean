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

theorem Ramification_Group_card_pos {u : ℚ} : 0 < Nat.card G(S/R)_[⌈u⌉] := by
  haveI : Finite G(S/R)_[⌈u⌉] := sorry
  refine Nat.card_pos

-- by definition of relindex, it's always 1 when u < 0
noncomputable def phiDeriv (u : ℚ) : ℚ :=
  --(Nat.card G(S/R)_[(⌈u⌉)] : ℚ) / (Nat.card G(S/R)_[0] : ℚ)
  --1 / Nat.card (G(S/R)_[0] ⧸ ((G(S/R)_[⌈u⌉]).subgroupOf G(S/R)_[0]))
  --1 / (relindex G(S/R)_[(⌈u⌉)] G(S/R)_[0])
  (Nat.card G(S/R)_[(max 0 ⌈u⌉)] : ℚ) / (Nat.card G(S/R)_[0] : ℚ)

noncomputable def phi (u : ℚ) : ℚ :=
  ∑ x in Finset.Icc 1 (⌈u⌉ - 1), (phiDeriv R S x) + (u - (max 0 (⌈u⌉ - 1))) * (phiDeriv R S u)

theorem phiDeriv_eq_one_of_le_zero {u : ℚ} (hu : u ≤ 0) : phiDeriv R S u = 1 := by
  unfold phiDeriv
  have hu' : ⌈u⌉ ≤ 0 := by exact ceil_nonpos hu
  simp only [hu', max_eq_left]
  apply div_self
  --card of ramigroup ne one
  apply ne_of_gt
  simp only [Nat.cast_pos]
  apply Ramification_Group_card_pos R S (u := 0)

theorem phi_eq_self_of_le_zero {u : ℚ} (hu : u ≤ 0) : phi R S u = u := by
  unfold phi
  simp [phiDeriv_eq_one_of_le_zero R S hu]
  have h : ⌈u⌉ - 1 ≤ 0 := by linarith [ceil_nonpos hu]
  have h' : ⌈u⌉ - 1 < 1 := by linarith [h]
  calc
    _ = (u - max 0 (⌈u⌉ - 1)) := by simp [h']
    _ = u := by simp [h]

theorem phiDeriv_pos (u : ℚ) : 0 < phiDeriv R S u := by
  unfold phiDeriv
  apply div_pos
  <;> simp only [Nat.cast_pos]
  have : max 0 ⌈u⌉ = ⌈max 0 (⌈u⌉ : ℚ)⌉ := by
    symm
    apply Int.ceil_eq_iff.2
    constructor
    · apply lt_of_lt_of_le (b := ↑(max 0 ⌈u⌉))
      linarith
      simp only [cast_max, cast_zero, le_refl]
    · simp only [cast_max, cast_zero, le_refl]
  rw [this]
  apply Ramification_Group_card_pos R S (u := max 0 ⌈u⌉)
  apply Ramification_Group_card_pos R S (u := 0)

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

theorem Finset.sum_Icc_sub_sum_Icc {n : ℤ} {m : ℤ} (hn : 1 ≤ n) (hnm : n ≤ m) : ∑ x in Finset.Icc 1 m, phiDeriv R S x - ∑ x in Finset.Icc 1 n, phiDeriv R S x = ∑ x in Finset.Icc (n + 1) m, phiDeriv R S x := by
  have hd : Disjoint (Finset.Icc 1 n) (Finset.Icc (n + 1) m) := by
    refine Disjoint.symm ((fun {α} {s t} ↦ Finset.disjoint_left.mpr) ?_)
    intro a ha
    rw [Finset.mem_Icc] at *
    apply not_and_or.2
    right
    linarith [ha.1]
  have hu : Finset.Icc 1 m = Finset.Icc 1 n ∪ Finset.Icc (n + 1) m := by
    ext x
    rw [Finset.mem_union]
    repeat rw [Finset.mem_Icc]
    constructor <;> intro h
    · by_cases hc : x ≤ n
      · left
        exact ⟨h.1, hc⟩
      · right
        exact ⟨by linarith [hc], h.2⟩
    · constructor
      · match h with
        | Or.inl h => exact h.left
        | Or.inr h => linarith [hn, h.right]
      · match h with
        | Or.inl h => linarith [h.left]
        | Or.inr h => exact h.right
  rw [sub_eq_iff_eq_add', hu]
  apply Finset.sum_union hd

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

theorem sum_insert_right_aux (a b : ℤ) (h : a ≤ b) (f : ℚ → ℚ) : (∑ x in Finset.Icc a b, f x) - f b = (∑ x in Finset.Icc a (b - 1), f x) := by sorry

theorem sum_insert_right_aux'' (a b : ℤ) (h : a ≤ b) (f : ℤ → ℚ) : (∑ x in Finset.Icc a b, f x) - f b = (∑ x in Finset.Icc a (b - 1), f x) := by sorry


theorem phi_strictMono_of_gt_one {a b : ℚ} (ha : 0 < a) (hb : 1 < b) (hab : a < b) : phi R S a < phi R S b := by
  unfold phi
  by_cases hceil : ⌈a⌉ = ⌈b⌉
  · simp only [hceil, phiDeriv_eq_ceil, ceil_intCast, cast_max, cast_zero, cast_sub, cast_one,
    add_lt_add_iff_left]
    apply (mul_lt_mul_right (by apply phiDeriv_pos R S)).2
    simp only [sub_lt_sub_iff_right, hab]
  · calc
      _ ≤ ∑ x in Finset.Icc 1 ⌈a⌉, phiDeriv R S x := by
        apply le_trans (b := ∑x in Finset.Icc 1 (⌈a⌉ - 1), phiDeriv R S ↑x + 1 * phiDeriv R S ⌈a⌉)
        rw [phiDeriv_eq_ceil R S]
        apply add_le_add_left
        apply (mul_le_mul_right (by apply phiDeriv_pos R S)).2
        have : a - 1 ≤ (max 0 (⌈a⌉ - 1)) := by
          simp only [cast_max, cast_zero, cast_sub, cast_one, le_max_iff, tsub_le_iff_right,
            zero_add, sub_add_cancel]
          right; apply le_ceil
        linarith [this]
        have h : ∑ x in Finset.Icc 1 (⌈a⌉ - 1), phiDeriv R S x + 1 * phiDeriv R S ⌈a⌉ = ∑ x in Finset.Icc 1 ⌈a⌉, phiDeriv R S x := by
            have h' : ∑ x in Finset.Icc 1 ⌈a⌉, phiDeriv R S x - 1 * phiDeriv R S ⌈a⌉ = ∑ x in Finset.Icc 1 (⌈a⌉ - 1), phiDeriv R S x := by
              by_cases hc : 1 ≤ a
              · rw [one_mul]
                apply sum_insert_right_aux 1 ⌈a⌉ ?_ (phiDeriv R S); exact one_le_ceil_iff.mpr ha
              · have h : ⌈a⌉ = 1 := by
                  refine ceil_eq_on_Ioc 1 a ?_
                  simp only [cast_one, sub_self, Set.mem_Ioc, ha, true_and]
                  apply le_of_lt; push_neg at hc; exact hc
                rw [h]; simp only [Finset.Icc_self, sum_singleton, cast_one, one_mul, sub_self, zero_lt_one, Finset.Icc_eq_empty_of_lt, sum_empty]
            exact add_eq_of_eq_sub (id (Eq.symm h'))
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
        apply  Finset.sum_le_sum_of_subset_of_nonneg h'
        intro i _ _
        apply le_of_lt
        apply phiDeriv_pos
      _ < phi R S b := by
        unfold phi
        simp only [cast_max, cast_zero, cast_sub, cast_one, lt_add_iff_pos_right]
        apply mul_pos
        simp only [sub_pos, max_lt_iff]
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
      simp only [cast_one, sub_self, ha0, ha1, and_self]
    · by_cases hb1 : b ≤ 1
      · push_neg at *
        have hbc : ⌈b⌉ = 1 := by
          apply ceil_eq_iff.2
          simp only [cast_one, sub_self, lt_trans ha0 h, hb1, and_self]
        have hceil : ⌈a⌉ = ⌈b⌉ := by simp [hac, hbc]
        have hderiv : phiDeriv R S a = phiDeriv R S b := by
          unfold phiDeriv
          simp only [hceil, one_div]
        rw [phi_of_pos_of_le_one R S ha0 ha1, phi_of_pos_of_le_one R S (by linarith) hb1]
        simp only [hderiv, gt_iff_lt]
        apply (mul_lt_mul_right (by apply phiDeriv_pos R S)).2 h
      · apply phi_strictMono_of_gt_one R S (by linarith) (by linarith) h
    apply phi_strictMono_of_gt_one R S (by linarith) (by linarith) h


theorem phi_Bijective : Function.Bijective (phi R S) := by
  constructor
  · rintro a1 a2 h
    contrapose! h
    by_cases h1 : a1 > a2
    · apply ne_of_gt (phi_strictMono R S h1)
    · push_neg at *
      apply ne_of_lt (phi_strictMono R S (lt_of_le_of_ne h1 h))
  · rintro y
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


@[simp]
theorem psi_phi_eq_self (u : ℚ) : (psi R S) ((phi R S) u) = u := by
  rw [← Function.comp_apply (f := psi R S) (g := phi R S)]
  unfold psi
  rw [Function.invFun_comp (f := (phi R S))]
  rfl; apply (phi_Bijective R S).injective


theorem psi_eq_self_of_le_neg_one {v : ℚ} (hv : v ≤ 0) : psi R S v = v := by
  have h1 : phi R S (psi R S v) = v := by apply phi_psi_eq_self
  have h2 : phi R S v = v := by apply phi_eq_self_of_le_zero R S hv
  apply (phi_Bijective R S).injective
  simp [h1, h2]

--lemma 3
open scoped Classical


variable (K L : Type*) {ΓK : outParam Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [vK : Valued K ℤₘ₀] [Valuation.IsDiscrete vK.v] [vL : Valued L ℤₘ₀] [Algebra K L] [IsValExtension K L] [FiniteDimensional K L]

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
    simp only [Finset.mem_inter]
    constructor
    · apply mem_of_subset_of_mem hu1 hs
    · apply mem_of_subset_of_mem hu2 hs
  apply le_trans hu
  rintro s hs
  simp at hs
  apply Ramification_Group_Disjoint K L hs.1 hs.2 hij

set_option synthInstance.maxHeartbeats 0

variable [CompleteSpace K] [Algebra.IsSeparable K L] -- [Algebra.IsSeparable (LocalRing.ResidueField ↥𝒪[K]) (LocalRing.ResidueField ↥𝒪[L])]

-- theorem mem_all_lowerRamificationGroup_iff_refl {x : (L ≃ₐ[K] L)}: (∀ n : ℤ, x ∈ G(L/K)_[n]) ↔ x = .refl := by
--   constructor <;> intro h
--   · by_contra hc
--     push_neg at hc
--     have hx : x = AlgEquiv.refl := by
--       obtain ⟨u, hu⟩ := exist_lowerRamificationGroup_eq_bot (K := K) (L := L)
--       replace h : x ∈ G(L/K)_[u] := by apply h u
--       rw [hu] at h
--       apply Subgroup.mem_bot.1 h
--     apply hc hx
--   · intro n
--     rw [h]
--     apply Subgroup.one_mem


theorem m_lt_n_of_in_G_m_of_notin_G_n {x : (L ≃ₐ[K] L)} {m n : ℤ} (hm : x ∈ G(L/K)_[m]) (hn : x ∉ G(L/K)_[n]) : m ≤ n - 1 := by
  by_contra hc
  push_neg at *
  have h : G(L/K)_[m] ≤  G(L/K)_[n] := by
    convert lowerRamificationGroup.antitone K L hc
    simp only [sub_add_cancel]
  apply hn
  apply Set.mem_of_subset_of_mem h hm

-- theorem aux_0 {x : L ≃ₐ[K] L} (hx : x ≠ .refl) : ∃ n : ℤ , x ∈ G(L/K)_[n] ∧ x ∉ G(L/K)_[(n + 1)] := by
--   by_contra hc; push_neg at hc
--   apply hx
--   apply (mem_all_lowerRamificationGroup_iff_refl K L).1
--   intro n
--   set t := n + 1; have : n = t - 1 := by ring
--   rw [this]
--   induction' t using Int.induction_on with m hm m hm
--   · simp only [zero_sub, reduceNeg]
--     rw [lowerRamificationGroup_eq_decompositionGroup, decompositionGroup_eq_top]
--     apply Subgroup.mem_top; rfl
--   · have : ((m : ℤ) + 1 - 1) = ((m : ℤ) - 1 + 1) := by simp only [add_sub_cancel_right,
--     sub_add_cancel]
--     rw [this]
--     apply hc (m - 1) hm
--   · rw [lowerRamificationGroup_eq_decompositionGroup, decompositionGroup_eq_top]
--     apply Subgroup.mem_top
--     simp only [reduceNeg, tsub_le_iff_right, add_left_neg, zero_add]
--     omega

-- theorem Raimification_Group_split (n : ℤ) : (⊤ : Finset (L ≃ₐ[K] L)) = (disjiUnion (Finset.Icc (-1) (n - 1)) (Ramification_Group_diff K L) (Ramification_Group_pairwiseDisjoint K L n)) ∪ (G(L/K)_[n] : Set (L ≃ₐ[K] L)).toFinset := by
--   ext x
--   constructor
--   · simp
--     by_cases hc : x ∉ G(L/K)_[n]
--     · left
--       unfold Ramification_Group_diff
--       have h : x ≠ .refl := by
--         by_contra hc1
--         apply hc
--         apply (mem_all_lowerRamificationGroup_iff_refl K L).2 hc1
--       obtain ⟨t, ht1, ht2⟩ := aux_0 K L h
--       use t
--       constructor
--       · constructor
--         --the index is greater than -1
--         · sorry
--         · apply m_lt_n_of_in_G_m_of_notin_G_n K L ht1 hc
--       · simp only [toFinset_diff, mem_sdiff, mem_toFinset, SetLike.mem_coe, ht1, ht2,
--         not_false_eq_true, and_self]
--     · push_neg at hc
--       right; exact hc
--   · intro h
--     simp only [Finset.top_eq_univ, Finset.mem_univ]

theorem aabb (a b : ℚ) : (1 / a) * b = b / a := by exact one_div_mul_eq_div a b

theorem phi_eq_sum_card {u : ℚ} (hu : 0 < u): phi K L u = (1 / Nat.card G(L/K)_[0]) * ((∑ x in Finset.Icc 1 (⌈u⌉ - 1), Nat.card G(L/K)_[x]) + (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈u⌉])) := by
  unfold phi phiDeriv
  calc
    _ = ∑ x ∈ Finset.Icc 1 (⌈u⌉ - 1), (Nat.card  G(L/K)_[⌈x⌉] : ℚ) / (Nat.card G(L/K)_[0] : ℚ) + (u - (max 0 (⌈u⌉ - 1))) * ((Nat.card G(L/K)_[⌈u⌉] ) / (Nat.card G(L/K)_[0] )) := by
      have h1 : ∑ x ∈ Finset.Icc 1 (⌈u⌉ - 1), (Nat.card G(L/K)_[(max 0 ⌈(x : ℚ)⌉)] : ℚ) / (Nat.card G(L/K)_[0] : ℚ)  = ∑ x ∈ Finset.Icc 1 (⌈u⌉ - 1), (Nat.card  G(L/K)_[⌈x⌉] : ℚ) / (Nat.card G(L/K)_[0] : ℚ) := by
        have h : ∀ i ∈ Finset.Icc 1 (⌈u⌉ - 1), max 0 ⌈(i : ℚ)⌉ = ⌈i⌉ := by
          intro i hi
          simp only [ceil_intCast, ceil_int, id_eq, max_eq_right_iff]
          rw [Finset.mem_Icc] at hi; linarith [hi.1]
        apply (Finset.sum_eq_sum_iff_of_le ?_).2
        · intro i hi
          rw [h i hi]
        · intro i hi
          rw [h i hi]
      have h2 :  (u - (max 0 (⌈u⌉ - 1))) * ((Nat.card G(L/K)_[(max 0 ⌈u⌉)] : ℚ) / (Nat.card G(L/K)_[0] : ℚ)) = (u - (max 0 (⌈u⌉ - 1))) * ((Nat.card G(L/K)_[⌈u⌉] : ℚ) / (Nat.card G(L/K)_[0] : ℚ)) := by
        have h : max 0 ⌈u⌉ = ⌈u⌉ := by
          apply max_eq_right
          apply le_of_lt; apply ceil_pos.2; exact hu
        rw [h]
      rw [h1, h2]
    _ = (1 / (Nat.card G(L/K)_[0] )) * ∑ x ∈ Finset.Icc 1 (⌈u⌉ - 1), (Nat.card G(L/K)_[⌈x⌉] ) + (u - (max 0 (⌈u⌉ - 1))) * ((Nat.card G(L/K)_[⌈u⌉] ) / (Nat.card G(L/K)_[0] )) := by
      congr
      convert (Finset.sum_div (Finset.Icc 1 (⌈u⌉ - 1)) (fun x => (Nat.card (lowerRamificationGroup K L ⌈x⌉) : ℚ)) (Nat.card ↥ G(L/K)_[0] : ℚ))
      · exact
        Eq.symm (sum_div (Finset.Icc 1 (⌈u⌉ - 1)) (fun i ↦ (Nat.card ↥ G(L/K)_[⌈i⌉] : ℚ)) (Nat.card ↥ G(L/K)_[0] : ℚ))
      · convert one_div_mul_eq_div (Nat.card G(L/K)_[0] : ℚ) ((∑ x ∈ Finset.Icc 1 (⌈u⌉ - 1), Nat.card ↥ G(L/K)_[⌈x⌉]) : ℚ)
        · exact Nat.cast_sum (Finset.Icc 1 (⌈u⌉ - 1)) fun x ↦ Nat.card ↥ G(L/K)_[⌈x⌉]
        · exact
          Eq.symm (sum_div (Finset.Icc 1 (⌈u⌉ - 1)) (fun i ↦ (Nat.card ↥ G(L/K)_[⌈i⌉] : ℚ)) (Nat.card ↥ G(L/K)_[0] : ℚ))
    _ = (1 / Nat.card G(L/K)_[0]) * ((∑ x in Finset.Icc 1 (⌈u⌉ - 1), Nat.card G(L/K)_[x]) + (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈u⌉])) := by
      rw [mul_add]
      congr 1
      rw [← mul_assoc, mul_comm (1 / (Nat.card G(L/K)_[0] : ℚ)), mul_assoc, one_div_mul_eq_div]


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
          simp only [add_sub_cancel_right]
        right_inv := by
          rintro x
          simp only [sub_add_cancel]
      }
      apply sum_equiv e
      rintro i
      constructor
      · simp only [reduceNeg, Finset.mem_Icc, and_imp]
        intro hi1 hi2
        simp only [Equiv.coe_fn_mk, add_one_le_ceil_iff, e]
        constructor
        · linarith [hi1]
        · apply add_one_le_ceil_iff.1 (by linarith [hi2])
      · simp only [Finset.mem_Icc, reduceNeg, and_imp]
        intro hi
        simp only [sub_nonneg, one_le_ceil_iff, Equiv.coe_fn_mk, add_one_le_ceil_iff, reduceNeg,
          e] at *
        intro hi'
        constructor
        · linarith [hi]
        · linarith [add_one_le_ceil_iff.2 hi']
      rintro i hi
      simp only [Nat.card_eq_fintype_card, Equiv.coe_fn_mk, e]
    _ = ((-1) + 1) * Nat.card G(L/K)_[(-1)] + ∑ i in Finset.Icc 0 (⌈u⌉ - 1), (i + 1) * Nat.card G(L/K)_[i] - ∑ i in Finset.Icc 0 (⌈u⌉ - 1), i * Nat.card G(L/K)_[i] - ⌈u⌉ * Nat.card G(L/K)_[⌈u⌉] := by
      have h : (-1) ≤ ⌈u⌉ - 1 := by linarith [hu]
      erw [← sum_insert_left_aux' (-1) (⌈u⌉ - 1) h (fun i => (i + 1) * Nat.card (lowerRamificationGroup K L i)), sub_sub, ← sum_insert_right_aux' 0 ⌈u⌉ (by linarith [h]) (fun i => i * Nat.card (lowerRamificationGroup K L i))]
      simp
    _ = ∑ i in Finset.Icc 0 (⌈u⌉ - 1), Nat.card G(L/K)_[i] - ⌈u⌉ * (Nat.card G(L/K)_[⌈u⌉]) := by
      rw [neg_add_self, zero_mul, zero_add]
      congr
      rw [← sum_sub_distrib]
      ring_nf
      exact Eq.symm (Nat.cast_sum (Finset.Icc 0 (-1 + ⌈u⌉)) fun x ↦ Nat.card ↥ G(L/K)_[x])

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
      sorry
      -- exact Set.card_le_card hsub


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
  sorry
  -- rw [Raimification_Group_split K L ⌈u⌉, sum_union, sum_disjiUnion]
  -- congr 1
  -- calc
  --   _ =  ∑ x in (G(L/K)_[⌈u⌉] : Set (L ≃ₐ[K] L)).toFinset , (u + 1) := by
  --     apply sum_equiv (by rfl : (L ≃ₐ[K] L) ≃ (L ≃ₐ[K] L)) (by simp)
  --     intro i hi
  --     apply truncatedLowerindex_eq_of_lt
  --     apply Set.mem_toFinset.1 hi
  --   _ = (u + 1) * (Nat.card G(L/K)_[⌈u⌉]) := by
  --     simp [← mul_sum (G(L/K)_[⌈u⌉] : Set (L ≃ₐ[K] L)).toFinset (fun _ => 1) (u + 1), add_mul, mul_comm]
  -- simp [Finset.disjoint_iff_ne]
  -- intro s n _ hn2 hs b hb
  -- unfold Ramification_Group_diff at *
  -- simp at hs
  -- rcases hs with ⟨_, hs2⟩
  -- by_contra h
  -- have h' : s ∈ G(L/K)_[⌈u⌉] := by
  --    rw [← h] at hb; exact hb
  -- have hs : s ∉ G(L/K)_[⌈u⌉] := by
  --   apply Set.not_mem_subset _ hs2
  --   apply lowerRamificationGroup.antitone
  --   linarith [hn2]
  -- apply hs h'


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
      --sorry
  · have hu' : 0 ≤ ⌈u⌉ - 1 := by
      push_neg at hu
      simp [add_one_le_ceil_iff.2 hu, hu]
    calc
      _ = (1 / Nat.card G(L/K)_[0]) * ((∑ i in Finset.Icc 1 (⌈u⌉ - 1), Nat.card G(L/K)_[i]) + (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈u⌉])) := by
        apply phi_eq_sum_card K L (by linarith [hu])
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
