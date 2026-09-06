import RACEFormal.AverageConcentration
import RACEFormal.CausalTriangle

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace RACEFormal

/--
Simultaneous two-sided concentration for the *averaged* RACE table score over
every causal query-key pair.  Each pair only needs independence across its own
`L` tables; no independence between different causal pairs is assumed.
-/
theorem causal_triangle_average_two_sided_union_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) {L : ℕ} (hL : 0 < L)
    (Z : CausalPair N → Fin L → Ω → ℝ)
    (mean : CausalPair N → ℝ)
    (hindep : ∀ p, iIndepFun (Z p) μ)
    (hmeas : ∀ p i, AEMeasurable (Z p i) μ)
    (hbound : ∀ p i, ∀ᵐ ω ∂μ, Z p i ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ p i, ∫ ω, Z p i ω ∂μ = mean p)
    {u : ℝ} (hu : 0 ≤ u) :
    μ.real (⋃ p : CausalPair N,
        {ω | u ≤ |((L : ℝ)⁻¹ * ∑ i, Z p i ω) - mean p|})
      ≤ (Fintype.card (CausalPair N) : ℝ) *
        (2 * Real.exp (-((L : ℝ) * u) ^ 2 /
          (2 * (∑ _i : Fin L, ((1 / 2 : ℝ≥0) ^ 2) : ℝ≥0)))) := by
  let bad : CausalPair N → Set Ω := fun p =>
    {ω | u ≤ |((L : ℝ)⁻¹ * ∑ i, Z p i ω) - mean p|}
  let q : ℝ := 2 * Real.exp (-((L : ℝ) * u) ^ 2 /
    (2 * (∑ _i : Fin L, ((1 / 2 : ℝ≥0) ^ 2) : ℝ≥0)))
  have hbad : ∀ p, μ.real (bad p) ≤ q := by
    intro p
    simpa [bad, q] using
      independent_bounded_table_scores_average_two_sided μ hL (Z p) (mean p)
        (hindep p) (hmeas p) (hbound p) (hmean p) hu
  simpa [bad, q] using
    finite_failure_union_bound_uniform μ bad q hbad

end RACEFormal
