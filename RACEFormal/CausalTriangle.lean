import RACEFormal.TwoSidedConcentration
import RACEFormal.UnionBound

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace RACEFormal

/-- A causal query-key index: row `t` together with a key position in its prefix. -/
abbrev CausalPair (N : ℕ) := Sigma fun t : Fin N => Fin (t.1 + 1)

/-- The number of causal pairs is the sum of the prefix lengths. -/
theorem card_causalPair_eq_prefix_sum (N : ℕ) :
    Fintype.card (CausalPair N) = ∑ t : Fin N, (t.1 + 1) := by
  simp [CausalPair, Fintype.card_sigma]

/--
Simultaneous two-sided concentration over every entry of the causal triangle.
No independence between distinct query-key pairs is needed: each pair only
requires independence across its own `L` table scores, and the final step is a
finite union bound.
-/
theorem causal_triangle_two_sided_union_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) {L : ℕ}
    (Z : CausalPair N → Fin L → Ω → ℝ)
    (mean : CausalPair N → Fin L → ℝ)
    (hindep : ∀ p, iIndepFun (Z p) μ)
    (hmeas : ∀ p i, AEMeasurable (Z p i) μ)
    (hbound : ∀ p i, ∀ᵐ ω ∂μ, Z p i ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ p i, ∫ ω, Z p i ω ∂μ = mean p i)
    {eps : ℝ} (heps : 0 ≤ eps) :
    μ.real (⋃ p : CausalPair N,
        {ω | eps ≤ |∑ i, (Z p i ω - mean p i)|})
      ≤ (Fintype.card (CausalPair N) : ℝ) *
        (2 * Real.exp (-eps ^ 2 /
          (2 * (∑ _i : Fin L, ((1 / 2 : ℝ≥0) ^ 2) : ℝ≥0)))) := by
  let bad : CausalPair N → Set Ω := fun p =>
    {ω | eps ≤ |∑ i, (Z p i ω - mean p i)|}
  let q : ℝ := 2 * Real.exp (-eps ^ 2 /
    (2 * (∑ _i : Fin L, ((1 / 2 : ℝ≥0) ^ 2) : ℝ≥0)))
  have hbad : ∀ p, μ.real (bad p) ≤ q := by
    intro p
    simpa [bad, q] using
      independent_bounded_table_scores_two_sided μ (Z p) (mean p)
        (hindep p) (hmeas p) (hbound p) (hmean p) heps
  simpa [bad, q] using
    finite_failure_union_bound_uniform μ bad q hbad

end RACEFormal
