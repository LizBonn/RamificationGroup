import RamificationGroup.LowerNumbering
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import RamificationGroup.Unused.MissingPiecesOfMathlib
import Mathlib.GroupTheory.Index
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Algebra.BigOperators.Basic

--definition of varphi and psi

open DiscreteValuation Subgroup Set Function MeasureTheory Finset BigOperators Int Valued

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [ValAlgebra R S]


noncomputable def Index_of_G_i (u : ℚ) : ℚ :=
  if u ≥ (-1) then
    relindex' G(S/R)_[0] G(S/R)_[(Int.ceil u)]
  else
    1

noncomputable def varphi' (u : ℚ) : ℚ :=
  1 / (Index_of_G_i R S u)

noncomputable def varphi (u : ℚ) : ℚ :=
  if u ≥ 1 then
    ∑ x in Finset.Icc 1 (Int.floor u), (varphi' R S x) + (u - (Int.floor u)) * (varphi' R S u)
  else
    u * (varphi' R S u)

theorem varphi_mono_int : ∀a1 a2 : ℤ , a1 < a2 → (varphi R S a1) < (varphi R S a2) := by
  rintro a1 a2 h
  induction' a2 with n ih
  sorry
  sorry

theorem varphi_mono_int' : ∀a1 a2 : ℤ , a1 ≤ a2 → (varphi R S a1) ≤ (varphi R S a2) := by
  rintro a1 a2 h
  by_cases heq : a1 = a2
  simp [heq]
  apply le_of_lt
  push_neg at *
  have hlt : a1 < a2 := by apply lt_of_le_of_ne h heq
  apply varphi_mono_int R S a1 a2 hlt

--i'll change this name
theorem varphi_rational_floor : ∀ a : ℚ , (varphi R S a) = (varphi R S ⌊a⌋) + ((varphi R S (⌊a⌋ + 1)) - (varphi R S ⌊a⌋)) * (a - ⌊a⌋) := by
  rintro a
  unfold varphi
  by_cases ha : a ≥ 1
  have hfl : 1 ≤ ↑⌊a⌋ := by apply le_floor.2 ha
  simp [ha, hfl]
  sorry
  have hfl : ¬ 1 ≤ ↑⌊a⌋ := by
    by_contra h'
    have h'' : 1 ≤ a := by apply le_floor.1 h'
    contradiction
  simp [ha, hfl]
  sorry

theorem varphi_rational_ceil : ∀ a : ℚ , (varphi R S a) = (varphi R S (⌊a⌋ + 1)) - ((varphi R S (⌊a⌋ + 1)) - (varphi R S ⌊a⌋)) * (⌊a⌋ - a + 1) := by
  rintro a
  unfold varphi
  by_cases ha : a ≥ 1
  have hcl : 1 ≤ (⌊a⌋ + 1) := by sorry
  simp [ha, hcl]
  sorry
  sorry

theorem varphi_gt_floor : ∀ a : ℚ , (a ≠ ⌊a⌋) → (varphi R S a) > (varphi R S ⌊a⌋) := by
  rintro a ha
  apply gt_iff_lt.2
  apply sub_lt_zero.1
  nth_rw 2 [varphi_rational_floor]
  simp
  apply mul_pos_iff.2
  left
  constructor
  simp
  sorry
  --apply varphi_mono_int R S ⌊a⌋ (⌊a⌋ + 1)
  apply fract_pos.2 ha

theorem varphi_lt_ceil : ∀ a : ℚ , (varphi R S a) < (varphi R S (⌊a⌋ + 1)) := by
  rintro a
  apply gt_iff_lt.2
  apply sub_lt_zero.1
  nth_rw 1 [varphi_rational_ceil]
  simp
  apply mul_pos_iff.2
  left
  constructor
  simp
  sorry
  --apply varphi_mono_int R S ⌊a⌋ (⌊a⌋ + 1)
  have : a - 1 < ⌊a⌋ := by apply sub_one_lt_floor
  linarith [this]

theorem varphi_mono_in_section : ∀ a1 a2 : ℚ , (⌊a1⌋ = ⌊a2⌋) ∧ (a1 < a2) → (varphi R S a1) < (varphi R S a2) := by
  rintro a1 a2 ⟨h1, h2⟩
  apply gt_iff_lt.2
  apply sub_lt_zero.1
  rw [varphi_rational_floor]
  sorry

--i'll change this name too
theorem varphi_mono_over_section : ∀ a1 a2 : ℚ , (⌊a1⌋ ≠ ⌊a2⌋) ∧ (a1 < a2) → (varphi R S a1) < (varphi R S a2) := by
  rintro a1 a2 ⟨hne, hlt⟩
  by_cases hfloor : a2 = ⌊a2⌋
  have hle : ⌊a1⌋ + 1 ≤ ⌊a2⌋ := by
    have hlt : ⌊a1⌋ < ⌊a2⌋ := by
      apply lt_of_le_of_ne
      apply floor_le_floor
      apply le_of_lt hlt
      apply hne
    apply add_one_le_of_lt hlt
  apply lt_of_lt_of_le
  have h1 : (varphi R S a1) < (varphi R S (⌊a1⌋ + 1)) := by apply (varphi_lt_ceil R S)
  apply h1
  have h2 : (varphi R S (⌊a1⌋ + 1)) ≤ (varphi R S a2) := by
    by_cases heq : (⌊a1⌋ + 1) = a2
    simp [heq]
    push_neg at heq
    have h1' : (varphi R S (⌊a1⌋ + 1)) ≤ (varphi R S ⌊a2⌋) := by
      sorry
      --apply varphi_mono_int' R S (⌊a1⌋ + 1) ⌊a2⌋
    rw [hfloor]
    exact h1'
  apply h2
  have hle : a1 ≤ ⌊a2⌋ := by
    by_contra hc
    push_neg at *
    have h : ⌊a1⌋ = ⌊a2⌋ := by
      have h1 : ⌊a1⌋ ≤ ⌊a2⌋ := by
        apply floor_le_floor
        apply le_of_lt
        exact hlt
      have h2 : ⌊a2⌋ ≤ ⌊a1⌋ := by
        apply le_floor.2
        apply le_of_lt hc
      apply (LE.le.ge_iff_eq h1).1 h2
    contradiction
  have hlt : ⌊a2⌋ < a2 := by
    have hge : ⌊a2⌋ ≤ a2 := by apply floor_le
    push_neg at hfloor
    apply lt_of_le_of_ne hge hfloor.symm
  apply lt_of_le_of_lt
  have h1 : (varphi R S a1) ≤ (varphi R S ⌊a2⌋) := by
    by_cases heq : a1 = ⌊a2⌋
    simp [heq]
    apply le_of_lt
    apply lt_of_lt_of_le
    push_neg at *
    have hlt' : a1 < ⌊a2⌋ := by apply lt_of_le_of_ne hle heq
    have h1' : (varphi R S a1) < (varphi R S (⌊a1⌋ + 1)) := by apply varphi_lt_ceil R S
    apply h1'
    have hle' : ⌊a1⌋ + 1 ≤ ⌊a2⌋ := by
      sorry
      --apply varphi_mono_int R S (⌊a1⌋ + 1) ⌊a2⌋
    have h2' : (varphi R S ↑(⌊a1⌋ + 1)) ≤ (varphi R S (⌊a2⌋)) := by
      apply varphi_mono_int' R S (⌊a1⌋ + 1) ⌊a2⌋ hle'
    sorry
    --apply h2'
  apply h1
  push_neg at hfloor
  have h2 : (varphi R S ⌊a2⌋) < (varphi R S a2) := by apply (varphi_gt_floor R S a2 hfloor)
  apply h2

theorem varphi_mono_iff : (∀a1 a2 : ℚ , a1 < a2 → (varphi R S a1) < (varphi R S a2)) ↔ (∀a1 a2 : ℤ , a1 < a2 → (varphi R S a1) < (varphi R S a2)) := by
  constructor
  rintro h a1 a2
  apply varphi_mono_int R S a1 a2
  rintro h a1 a2 h'
  by_cases hfloor : ⌊a1⌋ = ⌊a2⌋
  apply varphi_mono_in_section
  constructor <;> assumption
  push_neg at *
  apply varphi_mono_over_section
  constructor <;> assumption

theorem varphi_mono : ∀a1 a2 : ℚ , a1 < a2 → (varphi R S a1) < (varphi R S a2) := by
  apply (varphi_mono_iff R S).2
  apply varphi_mono_int

theorem varphi_bij : Function.Bijective (varphi R S) := by
  constructor
  rintro a1 a2 h
  contrapose! h
  by_cases h1 : a1 > a2
  have hlt : (varphi R S a2) < (varphi R S a1) := by
    apply varphi_mono
    apply h1
  apply ne_of_gt hlt
  have hlt : (varphi R S a2) > (varphi R S a1) := by
    apply varphi_mono
    apply lt_of_not_ge
    push_neg at *
    exact lt_of_le_of_ne h1 h
  apply ne_of_lt hlt
  rintro b
  unfold varphi varphi'
  by_cases hb : b < 0
  sorry
  sorry

noncomputable def psi : ℚ → ℚ :=
  invFun (varphi R S)

theorem psi_bij : Function.Bijective (psi R S) := by
  constructor
  have hpsi: (invFun (varphi R S)).Injective :=
    (rightInverse_invFun (varphi_bij R S).2).injective
  exact hpsi
  apply invFun_surjective
  apply (varphi_bij R S).1

theorem varphi_zero_eq_zero : varphi R S 0 = 0 := by
  unfold varphi
  simp

noncomputable def psi' (v : ℚ): ℚ :=
  1 / (varphi' R S (psi R S v))

theorem psi_zero_eq_zero : psi R S 0 = 0 := by
  unfold psi
  nth_rw 1 [← varphi_zero_eq_zero R S]
  have : id 0 = (0 : ℚ) := by rfl
  nth_rw 2 [← this]
  have Inj : (varphi R S).Injective := by apply (varphi_bij R S).1
  rw [← invFun_comp Inj]
  simp

--lemma 3
open scoped Classical


variable (K L : Type*) {ΓK : outParam Type*} [Field K] [Field L] [LinearOrderedCommGroupWithZero ΓK] [vK : Valued K ΓK] [vS : Valued L ℤₘ₀] [ValAlgebra K L]

instance : Fintype (L ≃ₐv[K] L) where
  elems := by sorry
  complete := by sorry

#check Finset.sum_disjiUnion
#check Set.PairwiseDisjoint
#check disjiUnion
#check Finset (Subgroup (L ≃ₐv[K] L))
#check Finset (L ≃ₐv[K] L)
#check Finset G(L/K)_[10]
#check ((G(L/K)_[10] : Set (L ≃ₐv[K] L)) \ (G(L/K)_[11] : Set (L ≃ₐv[K] L))).toFinset
#check SDiff
#check (G(L/K)_[(-1)] : Set (L ≃ₐv[K] L)).toFinset

noncomputable def G_diff (i : ℤ) : Finset (L ≃ₐv[K] L) := ((G(L/K)_[i] : Set (L ≃ₐv[K] L)) \ (G(L/K)_[(i + 1)] : Set (L ≃ₐv[K] L))).toFinset

theorem G_pairwiseDisjoint (n : ℤ) : (PairwiseDisjoint (↑(Finset.Icc (-1) (n - 1))) (G_diff K L)) := by
  induction' n with n ih
  induction' n with n ih
  simp
  sorry
  sorry

theorem G_n_or_G_lt_n {n : ℤ} (x : (L ≃ₐv[K] L)) (h : x ∉ G(L/K)_[n]) : ∃ a, (-1 ≤ a ∧ a ≤ n - 1) ∧ x ∈ G_diff K L a := by
  sorry

theorem G_split (n : ℤ) : (⊤ : Finset (L ≃ₐv[K] L)) = (disjiUnion (Finset.Icc (-1) (n - 1)) (G_diff K L) (G_pairwiseDisjoint K L n)) ∪ (G(L/K)_[n] : Set (L ≃ₐv[K] L)).toFinset := by
  ext x
  constructor
  simp
  by_cases h : x ∈ G(L/K)_[n]
  · right
    assumption
  left
  apply G_n_or_G_lt_n K L x h
  simp

theorem Sum_Trunc_lower_Index_of_G_n (n : ℤ) (u : ℚ) (h : u ≤ n) : (Finset.sum (G(L/K)_[n] : Set (L ≃ₐv[K] L)).toFinset ((ValAlgEquiv.truncatedLowerIndex K L · (u + 1)))) = (u + 1) * (Nat.card (G(L/K)_[n])) := by
  calc
  (Finset.sum (G(L/K)_[n] : Set (L ≃ₐv[K] L)).toFinset ((ValAlgEquiv.truncatedLowerIndex K L · (u + 1)))) = Finset.sum (G(L/K)_[n] : Set (L ≃ₐv[K] L)).toFinset (fun (x : _) => u + 1) := by
    apply sum_equiv (.refl (L ≃ₐv[K] L))
    simp
    rintro s hs
    sorry
  _ = (u + 1) * (Nat.card (G(L/K)_[n])) := by
    norm_num
    ring

theorem Sum_Trunc_lower_Index_of_diff_G (n : ℤ) (u : ℚ) (h : n ≤ u) : (Finset.sum (G_diff K L n) ((ValAlgEquiv.truncatedLowerIndex K L · (u + 1)))) = (n + 1) * (Nat.card (G_diff K L n)) := by
  calc
  (Finset.sum (G_diff K L n) ((ValAlgEquiv.truncatedLowerIndex K L · (u + 1)))) = (Finset.sum (G_diff K L n) (fun (x : _) => ((n : ℚ) + 1))) := by
    apply sum_equiv (.refl (L ≃ₐv[K] L))
    simp
    rintro s hs
    sorry
  _ = (n + 1) * (Nat.card (G_diff K L n)) := by
    norm_num
    ring

theorem Varphi_eq_Sum_Inf (u : ℚ) : (varphi K L u) = (1 / Nat.card G(L/K)_[0]) * ((Finset.sum (⊤ : Finset (L ≃ₐv[K] L)) (ValAlgEquiv.truncatedLowerIndex K L · (u + 1)))) - 1 := by
  by_cases h : u ≥ 1
  · simp [h]
    have hsplit : (Finset.sum (⊤ : Finset (L ≃ₐv[K] L)) (ValAlgEquiv.truncatedLowerIndex K L · (u + 1))) = (Finset.sum (((disjiUnion (Finset.Icc (-1) (⌈u⌉ - 1)) (G_diff K L) (G_pairwiseDisjoint K L _)))) ((ValAlgEquiv.truncatedLowerIndex K L · (u + 1)))) + (Finset.sum (((G(L/K)_[(⌈u⌉)] : Set (L ≃ₐv[K] L)).toFinset)) ((ValAlgEquiv.truncatedLowerIndex K L · (u + 1)))) := by
      calc
      (Finset.sum (⊤ : Finset (L ≃ₐv[K] L)) (ValAlgEquiv.truncatedLowerIndex K L · (u + 1))) = (Finset.sum (((disjiUnion (Finset.Icc (-1) (⌈u⌉ - 1)) (G_diff K L) (G_pairwiseDisjoint K L _)) ∪ (G(L/K)_[(⌈u⌉)] : Set (L ≃ₐv[K] L)).toFinset)) ((ValAlgEquiv.truncatedLowerIndex K L · (u + 1)))) := by
        congr
        apply G_split
      _ = (Finset.sum (((disjiUnion (Finset.Icc (-1) (⌈u⌉ - 1)) (G_diff K L) (G_pairwiseDisjoint K L _)))) ((ValAlgEquiv.truncatedLowerIndex K L · (u + 1)))) + (Finset.sum (((G(L/K)_[(⌈u⌉)] : Set (L ≃ₐv[K] L)).toFinset)) ((ValAlgEquiv.truncatedLowerIndex K L · (u + 1)))) := by
        have : Disjoint (disjiUnion (Finset.Icc (-1) (⌈u⌉ - 1)) (G_diff K L) (G_pairwiseDisjoint K L _)) (toFinset ↑ G(L/K)_[⌈u⌉]) := by sorry
        apply sum_union
        apply this
    have hsplit' : (Finset.sum (((disjiUnion (Finset.Icc (-1) (⌈u⌉ - 1)) (G_diff K L) (G_pairwiseDisjoint K L _)))) ((ValAlgEquiv.truncatedLowerIndex K L · (u + 1)))) = Finset.sum _ fun (i : ℤ) => Finset.sum _ fun (x : _) => (ValAlgEquiv.truncatedLowerIndex K L x (u + 1)) := by
      apply sum_disjiUnion
    simp at hsplit hsplit'
    rw [hsplit, hsplit']
    have hu : (Finset.sum ((G(L/K)_[(⌈u⌉)] : Set (L ≃ₐv[K] L)).toFinset) ((ValAlgEquiv.truncatedLowerIndex K L · (u + 1)))) = (u + 1) * (Nat.card G(L/K)_[⌈u⌉]) := by
      convert Sum_Trunc_lower_Index_of_G_n K L ⌈u⌉ u (by apply le_ceil)
    rw [hu]
    have hd : Finset.sum (Finset.Icc (-1) (⌈u⌉ - 1)) (fun (i : ℤ) => Finset.sum (G_diff K L i) (fun (x : _) => (ValAlgEquiv.truncatedLowerIndex K L x (u + 1)))) = Finset.sum (Finset.Icc (-1) (⌈u⌉ - 1)) fun (i : ℤ) => (i + 1) * (Nat.card ((G(L/K)_[i] : Set (L ≃ₐv[K] L)) \ G(L/K)_[(i + 1)] : Set (L ≃ₐv[K] L))):= by
      norm_num
      apply sum_equiv (.refl ℤ)
      simp
      simp
      rintro i hge hle
      have hle' : i ≤ u := by
        sorry
      convert Sum_Trunc_lower_Index_of_diff_G K L i u hle'
      unfold G_diff
      simp
      sorry
    rw [hd]
    sorry
  unfold varphi
  simp [h]
  sorry
