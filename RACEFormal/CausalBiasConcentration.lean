import RACEFormal.CausalTriangleAverage

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace RACEFormal

/--
A deterministic uniform bias bound can be added directly to the simultaneous
causal-triangle concentration radius.

If the averaged table score for every causal pair concentrates within `u` of
its own mean and every mean is within `B` of the target score, then failure of
the final `u + B` target guarantee is contained in the original concentration
failure event.  Consequently the same finite causal-triangle union bound
controls the complete bias-plus-variance error.
-/
theorem causal_triangle_average_bias_variance_union_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) {L : ℕ} (hL : 0 < L)
    (Z : CausalPair N → Fin L → Ω → ℝ)
    (mean target : CausalPair N → ℝ)
    (hindep : ∀ p, iIndepFun (Z p) μ)
    (hmeas : ∀ p i, AEMeasurable (Z p i) μ)
    (hbound : ∀ p i, ∀ᵐ ω ∂μ, Z p i ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ p i, ∫ ω, Z p i ω ∂μ = mean p)
    {u B : ℝ} (hu : 0 ≤ u)
    (hbias : ∀ p, |mean p - target p| ≤ B) :
    μ.real (⋃ p : CausalPair N,
        {ω | u + B ≤ |((L : ℝ)⁻¹ * ∑ i, Z p i ω) - target p|})
      ≤ (Fintype.card (CausalPair N) : ℝ) *
        (2 * Real.exp (-((L : ℝ) * u) ^ 2 /
          (2 * (∑ _i : Fin L, ((1 / 2 : ℝ≥0) ^ 2) : ℝ≥0)))) := by
  let meanBad : CausalPair N → Set Ω := fun p =>
    {ω | u ≤ |((L : ℝ)⁻¹ * ∑ i, Z p i ω) - mean p|}
  let targetBad : CausalPair N → Set Ω := fun p =>
    {ω | u + B ≤ |((L : ℝ)⁻¹ * ∑ i, Z p i ω) - target p|}
  have hsubset : (⋃ p, targetBad p) ⊆ ⋃ p, meanBad p := by
    intro ω hω
    rcases Set.mem_iUnion.mp hω with ⟨p, hp⟩
    apply Set.mem_iUnion.mpr
    refine ⟨p, ?_⟩
    change u ≤ |((L : ℝ)⁻¹ * ∑ i, Z p i ω) - mean p|
    by_contra hnot
    have hlt : |((L : ℝ)⁻¹ * ∑ i, Z p i ω) - mean p| < u :=
      lt_of_not_ge hnot
    have hfinal :
        |((L : ℝ)⁻¹ * ∑ i, Z p i ω) - target p| < u + B := by
      calc
        |((L : ℝ)⁻¹ * ∑ i, Z p i ω) - target p|
            = |(((L : ℝ)⁻¹ * ∑ i, Z p i ω) - mean p) +
                (mean p - target p)| := by ring_nf
        _ ≤ |((L : ℝ)⁻¹ * ∑ i, Z p i ω) - mean p| +
              |mean p - target p| := abs_add_le _ _
        _ < u + B := add_lt_add_of_lt_of_le hlt (hbias p)
    change u + B ≤ |((L : ℝ)⁻¹ * ∑ i, Z p i ω) - target p| at hp
    exact (not_lt_of_ge hp) hfinal
  calc
    μ.real (⋃ p : CausalPair N, targetBad p)
        ≤ μ.real (⋃ p : CausalPair N, meanBad p) :=
          measureReal_mono hsubset
    _ ≤ (Fintype.card (CausalPair N) : ℝ) *
        (2 * Real.exp (-((L : ℝ) * u) ^ 2 /
          (2 * (∑ _i : Fin L, ((1 / 2 : ℝ≥0) ^ 2) : ℝ≥0)))) := by
          simpa [meanBad] using
            causal_triangle_average_two_sided_union_bound
              μ N hL Z mean hindep hmeas hbound hmean hu

end RACEFormal
