import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Flat.Basic

universe u

open TensorProduct BigOperators Pointwise
variable (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]

#check Submodule.nontrivial_iff

theorem Faithfully_flat1 : (Module.Flat R M ∧ ∀(N : Type u) [AddCommGroup N] [Module R N],
    Nontrivial N → Nontrivial (M ⊗[R] N)) → (Module.Flat R M ∧ ∀(I : Ideal R) (hI : I ≠ ⊤),
    I • (⊤ : Submodule R M) ≠ ⊤) := by
    intro ⟨h1, h2⟩
    constructor
    · exact h1
    · intro I hI
      have h1 : Nontrivial (M ⊗[R] (R ⧸ I)):= by
        apply h2
        exact Ideal.Quotient.nontrivial hI
      have h2 : Nontrivial (M ⧸ (I • (⊤ : Submodule R M))) := by
        have : (M ⊗[R] (R ⧸ I)) = (M ⧸ (I • (⊤ : Submodule R M))) := by sorry
        rw [← this]
        exact h1
      have h3 : ∃ x ∈ (⊤ : Submodule R M), x ∉ (I • (⊤ : Submodule R M)) := by
        obtain ⟨s, hs⟩ :=  (nontrivial_iff_exists_ne 0).1 h2
        use s.
      by_contra hc
      have h4 : ∀ x ∈ (⊤ : Submodule R M), x ∈ (I • (⊤ : Submodule R M)) := by sorry
      absurd h3; push_neg; exact h4
