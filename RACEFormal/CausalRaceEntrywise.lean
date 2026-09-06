import RACEFormal.FactorizedTableExpectation
import RACEFormal.CausalBiasConcentration

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace RACEFormal

/--
End-to-end entrywise causal RACE guarantee for factorized soft table scores.
Each table is a product of `Pbits` independent soft bit factors, every bit has
the canonical one-bit soft RACE mean for the pair angle, and tables are
independent across the `L` repetitions for each causal pair.

The conclusion is a simultaneous high-probability bound over the whole causal
triangle against the exact powered angular kernel.
-/
theorem causal_race_factorized_entrywise_union_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) {L Pbits : ℕ} (hL : 0 < L)
    (W : CausalPair N → Fin L → Fin Pbits → Ω → ℝ)
    (alpha : CausalPair N → ℝ)
    (beta : ℝ) (hbeta : 0 < beta)
    (halpha0 : ∀ p, 0 < alpha p)
    (halphapi : ∀ p, alpha p < Real.pi)
    (hbitindep : ∀ p i, iIndepFun (W p i) μ)
    (hbitmeas : ∀ p i k, AEStronglyMeasurable (W p i k) μ)
    (hbitmean : ∀ p i k,
      ∫ ω, W p i k ω ∂μ =
        ∫ z, softBitAgreement beta z.2 (rotatedGaussianMargin (alpha p) z)
          ∂standardGaussianPlane)
    (htableindep : ∀ p,
      iIndepFun (fun i ω => ∏ k, W p i k ω) μ)
    (htablemeas : ∀ p i,
      AEMeasurable (fun ω => ∏ k, W p i k ω) μ)
    (htablebound : ∀ p i,
      ∀ᵐ ω ∂μ, (∏ k, W p i k ω) ∈ Set.Icc (0 : ℝ) 1)
    {u : ℝ} (hu : 0 ≤ u) :
    μ.real (⋃ p : CausalPair N,
        {ω |
          u + (Pbits : ℝ) * twoMarginLeakageBudget beta ≤
            |((L : ℝ)⁻¹ * ∑ i, ∏ k, W p i k ω) -
              (1 - alpha p / Real.pi) ^ Pbits|})
      ≤ (Fintype.card (CausalPair N) : ℝ) *
        (2 * Real.exp (-((L : ℝ) * u) ^ 2 /
          (2 * (∑ _i : Fin L, ((1 / 2 : ℝ≥0) ^ 2) : ℝ≥0)))) := by
  have htablemean : ∀ p i,
      ∫ ω, (∏ k, W p i k ω) ∂μ =
        (∫ z, softBitAgreement beta z.2
            (rotatedGaussianMargin (alpha p) z) ∂standardGaussianPlane) ^ Pbits := by
    intro p i
    exact factorized_soft_table_expectation_eq_power
      μ (W p i) (hbitindep p i) (hbitmeas p i)
      (alpha p) beta (hbitmean p i)
  have hbias : ∀ p,
      |(∫ z, softBitAgreement beta z.2
            (rotatedGaussianMargin (alpha p) z) ∂standardGaussianPlane) ^ Pbits -
        (1 - alpha p / Real.pi) ^ Pbits| ≤
        (Pbits : ℝ) * twoMarginLeakageBudget beta := by
    intro p
    exact powered_softBitAgreement_vs_angular_kernel_bias_le
      (alpha p) (halpha0 p) (halphapi p) Pbits beta hbeta
  simpa using
    (causal_triangle_average_bias_variance_union_bound
      μ N hL
      (fun p i ω => ∏ k, W p i k ω)
      (fun p =>
        (∫ z, softBitAgreement beta z.2
          (rotatedGaussianMargin (alpha p) z) ∂standardGaussianPlane) ^ Pbits)
      (fun p => (1 - alpha p / Real.pi) ^ Pbits)
      htableindep htablemeas htablebound htablemean hu hbias)

end RACEFormal
