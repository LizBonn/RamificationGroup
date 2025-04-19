import Mathlib.Tactic

noncomputable section

open scoped Classical

open Polynomial Finset IsPrimitiveRoot

variable {R : Type*} [CommRing R] [IsReduced R] [IsDomain R]
#check nthRoots
#check Finset.filter

structure IsPrimitiveRoot_aux (ζ : R) (k : ℕ) : Prop where
  pow_eq_one : ζ ^ (k : ℕ) = 1
  dvd_of_pow_eq_one : ∀ l : ℕ, ζ ^ l = 1 → k ∣ l

def primitiveRoots_aux (k : ℕ) (R : Type*) [CommRing R] [IsDomain R] : Finset R :=
  (nthRoots k (1 : R)).toFinset.filter fun ζ => IsPrimitiveRoot ζ k

def cyclotomic'_aux  (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] : R[X] :=
  ∏ μ ∈ primitiveRoots_aux n R, (X - C μ)

#check Finset.prod_mk
#check RingHom.map_one
#check monic_X_pow_sub_C
#check prod_multiset_X_sub_C_of_monic_of_roots_card_eq
#check prod_multiset_X_sub_C_of_monic_of_roots_card_eq
#check natDegree_X_pow_sub_C
#check IsPrimitiveRoot.card_nthRoots_one

theorem X_pow_sub_one_eq_prod_aux {ζ : R} {n : ℕ} (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
    X ^ n - 1 = ∏ ζ ∈ nthRootsFinset n R, (X - C ζ) := by
  classical
  rw [nthRootsFinset, ← Multiset.toFinset_eq (IsPrimitiveRoot.nthRoots_one_nodup h)]
  have h' : ∏ ζ ∈ { val := nthRoots n (1 : R), nodup := (nthRoots_one_nodup h) }, (X - C ζ) = (Multiset.map (fun ζ ↦ X - C ζ) (nthRoots n (1 : R))).prod := by sorry
  rw [h', nthRoots]
  have hmonic : (X ^ n - C (1 : R)).Monic := by sorry
  symm
  sorry

#check Finset.prod_biUnion
#check nthRoots_one_eq_biUnion_primitiveRoots
#check IsPrimitiveRoot.disjoint

theorem prod_cyclotomic'_eq_X_pow_sub_one_aux {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : ℕ}
    (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
    ∏ i ∈ Nat.divisors n, cyclotomic' i K = X ^ n - 1 := by
  classical
  have hd : (n.divisors : Set ℕ).PairwiseDisjoint fun k => primitiveRoots k K := by
    intro d hd y hy hdy
    sorry
  sorry


