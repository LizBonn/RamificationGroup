import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Topology.Algebra.Valuation
import Mathlib.Algebra.Order.WithZero
import Mathlib.Algebra.Order.Group.TypeTags
import Mathlib.FieldTheory.Galois
import LocalClassFieldTheory.LocalField
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal

open Classical multiplicity


open DiscreteValuation



#check Ideal.uniqueFactorizationMonoid



/-- `multiplicity a b` returns the largest natural number `n` such that
  `a ^ n ∣ b`, as a `PartENat` or natural with infinity. If `∀ n, a ^ n ∣ b`,
  then it returns `⊤`-/
def multiplicity' [Monoid α] [DecidableRel ((· ∣ ·) : α → α → Prop)] (a b : α) : PartENat :=
  PartENat.find fun n => ¬a ^ (n + 1) ∣ b

theorem finite_nat_iff' {a b : ℕ} : Finite a b ↔ a ≠ 1 ∧ 0 < b := by sorry
--   rw [← not_iff_not, not_finite_iff_forall, not_and_or, Ne.def, Classical.not_not, not_lt,
--     le_zero_iff]
--   exact
--     ⟨fun h =>
--       or_iff_not_imp_right.2 fun hb =>
--         have ha : a ≠ 0 := fun ha => hb <| zero_dvd_iff.mp <| by rw [ha] at h; exact h 1
--         Classical.by_contradiction fun ha1 : a ≠ 1 =>
--           have ha_gt_one : 1 < a :=
--             lt_of_not_ge fun _ =>
--               match a with
--               | 0 => ha rfl
--               | 1 => ha1 rfl
--               | b+2 => by linarith
--           not_lt_of_ge (le_of_dvd (Nat.pos_of_ne_zero hb) (h b)) (lt_pow_self ha_gt_one b),
--       fun h => by cases h <;> simp [*]⟩
-- #align multiplicity.finite_nat_iff multiplicity.finite_nat_iff

/-- For `p ≠ 1`, the `p`-adic valuation of a natural `n ≠ 0` is the largest natural number `k` such
that `p^k` divides `z`. If `n = 0` or `p = 1`, then `padicValNat p q` defaults to `0`. -/
def padicValNat' (p : ℕ) (n : ℕ) : ℕ :=
  if h : p ≠ 1 ∧ 0 < n then (multiplicity p n).get (multiplicity.finite_nat_iff.2 h) else 0


theorem finite_ideal_iff {A : Type u_2}  [CommRing A] [IsDomain A] [IsDedekindDomain A]
    {p : Ideal A} [Ideal.IsMaximal p] {a : A} :
    multiplicity.Finite p (Ideal.span {a}) ↔ a ≠ 0:= sorry


noncomputable abbrev ord {K : Type _} [Field K] [NumberField K]
    (p : Ideal (NumberField.ringOfIntegers K))
    [Ideal.IsMaximal p] (x : (NumberField.ringOfIntegers K)) : PartENat :=
    (multiplicity p (Ideal.span {x}))

-- variable {K : Type _} [Field K] [NumberField K] (p : Ideal (NumberField.ringOfIntegers K))
-- #synth IsDedekindDomain (NumberField.ringOfIntegers K)

theorem ord_top {K : Type _} [Field K] [NumberField K]
    {p : Ideal (NumberField.ringOfIntegers K)}
    [Ideal.IsMaximal p] {x : (NumberField.ringOfIntegers K)}
    : ord p x ≠ ⊤ → x ≠ 0 := sorry

noncomputable def exp_ord {K : Type _} [Field K] [NumberField K]
    (p : Ideal (NumberField.ringOfIntegers K))
    [Ideal.IsMaximal p] (x : (NumberField.ringOfIntegers K)) : NNReal :=
    if h : ord p x = ⊤ then 0 else (1/2) ^ ((ord p x).get (finite_ideal_iff.mpr (ord_top h)))


-- DiscreteValuation.termℤₘ₀ (open discretevaluation)


namespace DiscreteValuation

variable {K L : Type*} [Field K] [vK : Valued K ℤₘ₀] [Field L] [Algebra K L] [IsDiscrete vK.v] [CompleteSpace K] {K' : IntermediateField K L} [FiniteDimensional K K']

instance valuedIntermediateField : Valued K' ℤₘ₀ := DiscreteValuation.Extension.valued K K'

/- -- success
#synth IsDiscrete (valuedIntermediateField.v : Valuation K' _)
-/

-- this is needed, or #synth CompleteSpace K' fails
-- `when is this needed?`
instance (priority := 100) : CompleteSpace K' := DiscreteValuation.Extension.completeSpace K K'

end DiscreteValuation
