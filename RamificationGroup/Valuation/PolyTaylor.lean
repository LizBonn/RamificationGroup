/-
GOAL:
1. one order taylor expansion
-/
import Mathlib.Data.Polynomial.Taylor

namespace Polynomial

#check Polynomial.aeval_def -- `aeval` seems useless, but it is used in `minpoly` :(
#check Polynomial.eval_map -- ev(x) ∘ map(φ) = ev₂(x, φ)
#check Polynomial.eval₂_map -- ev₂(x, ψ) ∘ map(φ) = ev₂(x, ψ ∘ φ)
#check Polynomial.hom_eval₂ -- ψ ∘ ev₂(x, φ) = ev₂(ψ(x), ψ ∘ φ)

section hasse

variable {A : Type*}

theorem hasseDeriv_coeff_zero [Semiring A] (f : A[X]) (k : ℕ) :
  ((hasseDeriv k) f).coeff 0 = f.coeff k := by
  rw [hasseDeriv_coeff]
  simp only [zero_add, Nat.choose_self, Nat.cast_one, one_mul]

theorem hasseDeriv_coeff_one [CommSemiring A] (f : A[X]) (k : ℕ) :
  ((hasseDeriv k) f).coeff 1 = (derivative f).coeff k := by
  rw [hasseDeriv_coeff, coeff_derivative,
    add_comm 1 k, Nat.choose_succ_self_right, mul_comm]
  simp only [Nat.cast_add, Nat.cast_one]

theorem X_sq_dvd_hassDeriv_sub_coeff_sub_derivative_coeff [CommRing A] (f : A[X]) (k : ℕ) :
  X ^ 2 ∣ (hasseDeriv k) f - C (f.coeff k) - C ((derivative f).coeff k) * X := by
  rw [X_pow_dvd_iff]
  intro d hd
  match d with
  | 0 => simp only [coeff_sub, hasseDeriv_coeff_zero, coeff_C_zero, sub_self, mul_coeff_zero, coeff_X_zero, mul_zero]
  | 1 => simp only [coeff_sub, hasseDeriv_coeff_one, coeff_C_succ, sub_zero, coeff_mul_X, coeff_C_zero, sub_self]

end hasse

section taylor

variable {A : Type*} [CommRing A]
variable (f : A[X])
variable {B : Type*} [CommRing B]
variable (s : A →+* B)

theorem taylor_order_one (h : A) :
  ∃g : A[X], f.comp (X + C h) =
    f + (C h) * derivative f + (C h ^ 2) * g := by
  have : (C h) ^ 2 ∣ f.comp (X + C h) - f - (C h) * derivative f := by
    rw [← map_pow, C_dvd_iff_dvd_coeff]
    intro n
    simp only [coeff_sub, coeff_C_mul, ← taylor_apply, taylor_coeff]
    let h' := eval_dvd (x := h) <|X_sq_dvd_hassDeriv_sub_coeff_sub_derivative_coeff f n
    simp only [eval_pow, eval_X, eval_sub, eval_C, eval_mul] at h'
    rw [mul_comm]
    exact h'
  rcases this with ⟨g, hg⟩
  use g
  simp only [← hg, add_add_sub_cancel, add_sub_cancel'_right]

theorem taylor_order_one_apply (x h : A) :
  ∃gx : A, f.eval (x + h) =
    f.eval x + h * (derivative f).eval x + h ^ 2 * gx := by
  rcases taylor_order_one f h with ⟨g, exp⟩
  use g.eval x
  calc
    _ = (f.comp (X + C h)).eval x := by
      simp only [eval_comp, eval_add, eval_X, eval_C]
    _ = f.eval x + h * (derivative f).eval x + h ^ 2 * g.eval x := by
      simp only [exp, eval_add, eval_mul, eval_C, eval_pow]

theorem taylor_order_one_apply₂ (x h : B) :
  ∃gx : B, f.eval₂ s (x + h) =
    f.eval₂ s x + h * (derivative f).eval₂ s x + h ^ 2 * gx := by
  simp only [← eval_map]
  rcases taylor_order_one_apply (f.map s) x h with ⟨gx, exp⟩
  use gx
  simp only [exp, derivative_map]

theorem taylor_order_one_apply_aeval [Algebra A B] (x h : B) :
  ∃gx : B, aeval (x + h) f =
    aeval x f + h * aeval x (derivative f) + h ^ 2 * gx := by
  simp only [aeval_def, taylor_order_one_apply₂]

theorem taylor_order_zero_apply_aeval [Algebra A B] (x h : B) :
  ∃gx : B, aeval (x + h) f =
    aeval x f + h * gx := by
  rcases taylor_order_one_apply_aeval f x h with ⟨a, ha⟩
  use aeval x (derivative f) + h * a
  rw [ha]
  ring_nf

end taylor
