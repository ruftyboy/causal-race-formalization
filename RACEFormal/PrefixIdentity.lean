import Mathlib

open scoped BigOperators

namespace RACEFormal

/--
Algebraic identity behind the numerator update in causal RACE: querying cumulative
feature/value buckets is exactly the sum of per-key feature inner products times values.
This is the finite-dimensional prefix identity, independent of probability.
-/
theorem prefix_bucket_numerator_identity
    {m c : ℕ} {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (q : Fin c → ℝ) (k : Fin m → Fin c → ℝ) (V : Fin m → E) :
    (∑ r, q r • (∑ j, k j r • V j))
      = ∑ j, (∑ r, q r * k j r) • V j := by
  simp_rw [Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

/--
The analogous denominator identity: querying cumulative feature counts equals the
sum of per-key feature inner products.
-/
theorem prefix_bucket_denominator_identity
    {m c : ℕ} (q : Fin c → ℝ) (k : Fin m → Fin c → ℝ) :
    (∑ r, q r * (∑ j, k j r))
      = ∑ j, (∑ r, q r * k j r) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

end RACEFormal
