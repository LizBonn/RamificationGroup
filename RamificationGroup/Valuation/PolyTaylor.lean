/-
GOAL:
1. one order taylor expansion
-/
import Mathlib.Data.Polynomial.Taylor

namespace Polynomial

#check Polynomial.aeval_def -- `aeval` seems useless, but it is used in `minpoly` :(
#check Polynomial.eval_map -- ev(x) ∘ map(φ) = ev₂(x, φ)
#check Polynomial.eval₂_map -- ev₂(x, ψ) ∘ map(φ) = ev₂(x, ψ ∘ φ)
#check Polynomial.hom_eval₂ -- ψ ∘ ev(x, φ) = ev₂(ψ(x), ψ ∘ φ)


variable {A : Type*} [CommSemiring A]
variable (f : A[X])
variable {B : Type*} [CommSemiring B]
variable (s : A →+* B)

section taylor

theorem taylor_order_one (h : A) :
  ∃g : A[X], f.comp (X + C h) =
    f + (C h) * derivative f + (C h ^ 2) * g := by
  sorry

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

end taylor
