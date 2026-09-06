import RACEFormal.TwoSidedConcentration

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace RACEFormal

/--
Two-sided Hoeffding bound for the *average* of `L` independent `[0,1]` table
scores with a common mean.  The threshold in the sum-level theorem is `L * u`;
this is the form used directly by the RACE estimator.
-/
theorem independent_bounded_table_scores_average_two_sided
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {L : ℕ} (hL : 0 < L)
    (Z : Fin L → Ω → ℝ) (m : ℝ)
    (hindep : iIndepFun Z μ)
    (hmeas : ∀ i, AEMeasurable (Z i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, Z i ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ i, ∫ ω, Z i ω ∂μ = m)
    {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω |
        u ≤ |((L : ℝ)⁻¹ * ∑ i, Z i ω) - m|}
      ≤ 2 * Real.exp (-((L : ℝ) * u) ^ 2 /
          (2 * (∑ _i : Fin L, ((1 / 2 : ℝ≥0) ^ 2) : ℝ≥0))) := by
  have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
  have hsum := independent_bounded_table_scores_two_sided
    μ Z (fun _i => m) hindep hmeas hbound hmean
    (eps := (L : ℝ) * u) (mul_nonneg hLr.le hu)
  have hcenter (ω : Ω) :
      (∑ i, (Z i ω - m)) =
        (L : ℝ) * (((L : ℝ)⁻¹ * ∑ i, Z i ω) - m) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hLr.ne']
  have hevent :
      {ω | u ≤ |((L : ℝ)⁻¹ * ∑ i, Z i ω) - m|} =
        {ω | (L : ℝ) * u ≤ |∑ i, (Z i ω - m)|} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [hcenter, abs_mul, abs_of_pos hLr]
    constructor <;> intro h <;> nlinarith
  rw [hevent]
  exact hsum

end RACEFormal
