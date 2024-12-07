import Mathlib.Tactic

/-
# Main goal
  1.Take a second to learn about Type Theory.
  2.Learn Lean language ambiguously.
  3.State and proof a theorem in Lean.

# Cataloge
  1."#check" and very few Type Theory
  2.What do we use Lean for
  3*."variable" and implicit and explicit parameter
  4**.structure, class and instance
  5."rw", "have" and "apply"
  6.constructor, And and Or
  7.all and exist
  8.not and "push_neg"
  9*."rfl", "ring", "linarith" and "simp"
  10.LETS DO IT
-/

section one
/-
  # "#check" and very few Type Theory:
  1.Everything has a type.
  2.You can always use "#check" to check the type of everything.
  3.You can "ctrl + click" to turn to the source.
-/

#check 1
#check (1 : ℝ)
#check √2
#check 2 + 2
#check 2 + 2 = 4
#check mul_comm

end one

section two
/-
  # What do we use Lean for
  1.You can state and proof theorems in Lean.
  2.To do that, you have to be familiar with the syntax of Lean.
  3.And know what is already done in Mathlib, you can search it here : https://leanprover-community.github.io/mathlib4_docs/
  Here's a simple example
-/

theorem /-name-/The_frist_example /-parameters-/{G : Type*} [Group G] (a b c d e f : G) (h : a * b = c * d) (h' : e = f) : /-goal-/a * (b * e) = c * (d * f) := by/-proof-/
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

end two

section three
/-
  # "variable" and implicit and explicit parameter
  1.The variable keyword allows you to declare some parameters.
  2.You can declare it implicit with {} or explicit with ().
  3.It decide when you use a theorem, whether you need to give these parameters.
-/
#check lt_trans

variable {a b c : ℝ} (h1 : a < b) (h2 : b < c)

theorem The_second_example : a < c := by
  apply lt_trans h1 h2

end three

section four
/-
  # structure, class and instance
  1.The "structure" keyword allows you to collect some data together.
  2.Use the "class" keyword so Lean knows you want to use it.
  3.Use [] to give an instance.
-/

structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

structure IsLinear (f : ℝ → ℝ) where
  is_additive : ∀ x y, f (x + y) = f x + f y
  preserves_mul : ∀ x c, f (c * x) = c * f x

structure Group₁ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

class Group₂ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one


-- instance {α : Type*} : Group₂ (Equiv.Perm α) where
--   mul f g := Equiv.trans g f
--   one := Equiv.refl α
--   inv := Equiv.symm
--   mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
--   one_mul := Equiv.trans_refl
--   mul_one := Equiv.refl_trans
--   inv_mul_cancel := Equiv.self_trans_symm

variable {α : Type*} [Group₂ α] --[Group₁ α]


end four

section five
/-
  # "rw", "have" and "apply"
  1.The "rw" keyword meas rewrite, it allows you to rewrite your currently goal.
  2.The "have" keyword allows you to proof another goal first.
  3.The "apply" keyword allows you to apply some theorems to your goal.
  USE THESE TO MAKE A PROOF ON YOUR OWN!
-/
variable (a b c d e f : ℝ)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]

example : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

example (h₀ : 1 ≤ 2) (h₁ : 2 ≤ 3) : 1 ≤ 3 := by
  apply le_trans h₀ h₁
  -- · apply h₀
  -- · apply h₁
  -- apply le_trans h₀ h



end five
#check mul_sub
#check add_mul
#check sub_sub
#check sub_left_inj
#check mul_comm
#check add_sub_cancel_right
example{a b:ℝ}:(a+b)*(a-b)=a*a-b*b :=by
  rw[add_mul,mul_sub,mul_sub, add_sub,mul_comm a b,sub_add, sub_self,sub_zero ]

section six
/-:
  # constructor, And and Or
  1.(a ∧ b).left is a, (a ∧ b).right is b.
  2.constructor allows you to prove a statement of the form a ∧ b by proving a and then proving b.
-/
variable {x y : ℝ}

example (h₀ : x ≤ y) (h₁ : x ≠ y) : x ≤ y ∧ x ≠ y := by
  constructor
  · apply h₀
  · apply h₁

example (h : (y > 0) ∧ (y < 8)) : y > 0 ∨ y < -1 := by
  left
  apply h.left

end six

section seven
/-
  # all and exist
  1."intro" for "all" and "use" for "exist".
-/

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b := by
  intro a b hab
  apply h
  apply hab

example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 3
  constructor
  · norm_num
  · norm_num

end seven

section eight
/-
  # not and "push_neg"
-/
variable {x : ℝ}

example (h : x < 0) : ¬ 0 ≤ x := by
  push_neg
  apply h

end eight

section nine
/-
  # "rfl", "ring", "linarith" and "simp"
  1.you will love them
-/
variable (a b c d : ℝ)

example : a - b = a + -b :=
  rfl

example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by ring

example : c * b * a = b * (a * c) := by
  ring

example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith

end nine

section ten

variable {a b c d : ℝ}

#check mul_sub
#check add_mul
#check sub_sub
#check sub_left_inj
#check mul_comm
#check add_sub_cancel_right
example : (a + b) * (a - b) = a * a - b * b := by sorry

#check lt_of_le_of_ne
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  push_neg
  apply lt_of_le_of_ne h.left h.right

end ten

-- section ten

-- section Cyclic

-- open Finset Nat

-- variable {α : Type*} [Group α] [DecidableEq α] [Fintype α]
--   (hn : ∀ n : ℕ, 0 < n → (univ.filter fun a : α => a ^ n = 1).card ≤ n)

-- theorem isCyclic_of_orderOf_eq_card_aux [Fintype α] (x : α) (hx : orderOf x = Fintype.card α) :
--     IsCyclic α := by
--   classical
--     use x
--     simp_rw [← SetLike.mem_coe, ← Set.eq_univ_iff_forall]
--     rw [← Fintype.card_congr (Equiv.Set.univ α), ← Fintype.card_zpowers] at hx
--     exact Set.eq_of_subset_of_card_le (Set.subset_univ _) (ge_of_eq hx)

-- theorem isCyclic_of_card_pow_eq_one_le_aux : IsCyclic α := by
--   have : (univ.filter fun a : α => orderOf a = Fintype.card α).Nonempty := by
--     apply card_pos.1
--     rw [card_orderOf_eq_totient_aux₂ hn dvd_rfl, totient_pos]
--     apply Fintype.card_pos
--   let ⟨x, hx⟩ := this
--   apply isCyclic_of_orderOf_eq_card_aux x (Finset.mem_filter.1 hx).2

-- end Cyclic

-- section Polynomial

-- open Polynomial Multiset

-- variable {R : Type*} [CommRing R] [IsDomain R] {p q : R[X]}

-- theorem card_nthRoots (n : ℕ) (a : R) : Multiset.card (nthRoots n a) ≤ n := by
--   classical exact
--   (if hn : n = 0 then
--     if h : (X : R[X]) ^ n - C a = 0 then by
--       simp [Nat.zero_le, nthRoots, roots, h, dif_pos rfl, empty_eq_zero, Multiset.card_zero]
--     else by
--       apply WithBot.coe_le_coe.1
--       apply le_trans (card_roots h)
--       rw [hn, pow_zero, ← C_1, ← RingHom.map_sub]
--       exact degree_C_le
--   else by
--     rw [← Nat.cast_le (α := WithBot ℕ)]
--     rw [← degree_X_pow_sub_C (Nat.pos_of_ne_zero hn) a]
--     exact card_roots (X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) a))

-- end Polynomial

-- variable {F : Type*} [Field F] [Fintype Fˣ] [DecidableEq Fˣ]
-- #check FiniteField.roots_X_pow_card_sub_X
-- #check instIsCyclicUnitsOfFinite
-- #check isCyclic_of_card_pow_eq_one_le

-- theorem isCyclic_of_finite_field : IsCyclic Fˣ := by
--   apply isCyclic_of_card_pow_eq_one_le
--   intro n hn
--   apply le_trans
--   · apply card_nthRoots_subgroup_units (Units.coeHom F) Units.ext hn
--   · apply Polynomial.card_nthRoots

-- end ten
