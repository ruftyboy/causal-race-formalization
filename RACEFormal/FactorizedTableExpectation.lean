import RACEFormal.GaussianHardCollisionExpectation
import Mathlib.Probability.Independence.Integration

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RACEFormal

/--
The expectation of a product of finitely many independent scalar factors is
the product of their expectations.  When all factors have the same mean `g`,
this is exactly `g ^ Pbits`.
-/
theorem independent_identical_factors_expectation
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    {Pbits : ℕ}
    (W : Fin Pbits → Ω → ℝ)
    (hindep : iIndepFun W μ)
    (hmeas : ∀ i, AEStronglyMeasurable (W i) μ)
    (g : ℝ)
    (hmean : ∀ i, ∫ ω, W i ω ∂μ = g) :
    (∫ ω, ∏ i, W i ω ∂μ) = g ^ Pbits := by
  rw [hindep.integral_fun_prod_eq_prod_integral hmeas]
  simp_rw [hmean]
  simp

/--
An actual `Pbits`-factor table score whose independent factors all have the
canonical one-bit soft RACE expectation has mean equal to the corresponding
power of that one-bit expectation.
-/
theorem factorized_soft_table_expectation_eq_power
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    {Pbits : ℕ}
    (W : Fin Pbits → Ω → ℝ)
    (hindep : iIndepFun W μ)
    (hmeas : ∀ i, AEStronglyMeasurable (W i) μ)
    (alpha beta : ℝ)
    (hmean : ∀ i,
      ∫ ω, W i ω ∂μ =
        ∫ z, softBitAgreement beta z.2 (rotatedGaussianMargin alpha z)
          ∂standardGaussianPlane) :
    (∫ ω, ∏ i, W i ω ∂μ) =
      (∫ z, softBitAgreement beta z.2 (rotatedGaussianMargin alpha z)
        ∂standardGaussianPlane) ^ Pbits := by
  exact independent_identical_factors_expectation μ W hindep hmeas _ hmean

/--
Therefore an actual independent `Pbits` soft-RACE table score has mean within
`Pbits * twoMarginLeakageBudget beta` of the exact powered angular kernel.
This closes the gap between a power of a one-bit expectation and the
expectation of the product score used by a factorized RACE table.
-/
theorem factorized_soft_table_mean_bias_le_angular_kernel
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    {Pbits : ℕ}
    (W : Fin Pbits → Ω → ℝ)
    (hindep : iIndepFun W μ)
    (hmeas : ∀ i, AEStronglyMeasurable (W i) μ)
    (alpha : ℝ) (ha0 : 0 < alpha) (hapi : alpha < Real.pi)
    (beta : ℝ) (hbeta : 0 < beta)
    (hmean : ∀ i,
      ∫ ω, W i ω ∂μ =
        ∫ z, softBitAgreement beta z.2 (rotatedGaussianMargin alpha z)
          ∂standardGaussianPlane) :
    |(∫ ω, ∏ i, W i ω ∂μ) - (1 - alpha / Real.pi) ^ Pbits| ≤
      (Pbits : ℝ) * twoMarginLeakageBudget beta := by
  rw [factorized_soft_table_expectation_eq_power μ W hindep hmeas alpha beta hmean]
  exact powered_softBitAgreement_vs_angular_kernel_bias_le
    alpha ha0 hapi Pbits beta hbeta

end RACEFormal
