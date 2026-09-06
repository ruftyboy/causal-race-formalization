import Mathlib

open scoped BigOperators

namespace RACEFormal

/--
A product distribution on hypercube corners has total mass equal to the product
of its one-bit masses.  In particular, if every bit distribution is normalized,
the full corner distribution is normalized.
-/
theorem product_corner_mass_factorization
    (P : ℕ) (p : Fin P → Bool → ℝ) :
    (∑ v : Fin P → Bool, ∏ i, p i (v i)) = ∏ i, ∑ b : Bool, p i b := by
  simpa using (Fintype.prod_sum (fun i b => p i b)).symm

/--
Exact hypercube factorization used by soft RACE: the inner product of two
product-form corner distributions is the product of their one-bit agreement
factors.
-/
theorem product_corner_inner_factorization
    (P : ℕ) (p q : Fin P → Bool → ℝ) :
    (∑ v : Fin P → Bool, (∏ i, p i (v i)) * (∏ i, q i (v i)))
      = ∏ i, ∑ b : Bool, p i b * q i b := by
  simpa [Finset.prod_mul_distrib] using
    (Fintype.prod_sum (fun i b => p i b * q i b)).symm

/-- A normalized family of one-bit distributions yields a normalized corner distribution. -/
theorem product_corner_mass_one
    (P : ℕ) (p : Fin P → Bool → ℝ)
    (hbit : ∀ i, ∑ b : Bool, p i b = 1) :
    (∑ v : Fin P → Bool, ∏ i, p i (v i)) = 1 := by
  rw [product_corner_mass_factorization]
  simp_rw [hbit]
  simp

end RACEFormal
