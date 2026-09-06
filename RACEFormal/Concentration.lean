import Mathlib.Probability.Moments.SubGaussian

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace RACEFormal

/--
A centered random variable obtained from a score in `[0,1]` is sub-Gaussian
with Hoeffding parameter `1/4`.  This is the scalar fact needed for one fixed
query-key pair across independent RACE tables.
-/
theorem centered_unit_interval_subgaussian
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (m : ℝ)
    (hX : AEMeasurable X μ)
    (hbound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∫ ω, X ω ∂μ = m) :
    HasSubgaussianMGF (fun ω => X ω - m) ((1 / 2 : ℝ≥0) ^ 2) μ := by
  have h := hasSubgaussianMGF_of_mem_Icc (X := X) hX hbound
  simpa [hmean] using h

/-- Centering each member of an independent family preserves independence. -/
theorem center_preserves_iIndepFun
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {L : ℕ}
    (X : Fin L → Ω → ℝ) (m : Fin L → ℝ)
    (hindep : iIndepFun X μ) :
    iIndepFun (fun i ω => X i ω - m i) μ := by
  simpa [Function.comp_def] using
    hindep.comp (fun i x => x - m i) (fun _i => by fun_prop)

/--
Mathlib's Hoeffding theorem specialized to a finite family of independent
centered table scores with common sub-Gaussian parameter `1/4`.
-/
theorem independent_table_scores_upper_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {L : ℕ} (X : Fin L → Ω → ℝ)
    (hindep : iIndepFun X μ)
    (hsub : ∀ i, HasSubgaussianMGF (X i) ((1 / 2 : ℝ≥0) ^ 2) μ)
    {eps : ℝ} (heps : 0 ≤ eps) :
    μ.real {ω | eps ≤ ∑ i, X i ω}
      ≤ Real.exp (-eps ^ 2 /
          (2 * (∑ _i : Fin L, ((1 / 2 : ℝ≥0) ^ 2) : ℝ≥0))) := by
  simpa using
    (ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (μ := μ) hindep
      (c := fun _ : Fin L => ((1 / 2 : ℝ≥0) ^ 2))
      (s := Finset.univ)
      (fun i _hi => hsub i) heps)

/-- The matching lower-tail form, obtained by negating every centered score. -/
theorem independent_table_scores_lower_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {L : ℕ} (X : Fin L → Ω → ℝ)
    (hindep : iIndepFun X μ)
    (hsub : ∀ i, HasSubgaussianMGF (X i) ((1 / 2 : ℝ≥0) ^ 2) μ)
    {eps : ℝ} (heps : 0 ≤ eps) :
    μ.real {ω | eps ≤ -(∑ i, X i ω)}
      ≤ Real.exp (-eps ^ 2 /
          (2 * (∑ _i : Fin L, ((1 / 2 : ℝ≥0) ^ 2) : ℝ≥0))) := by
  let Y : Fin L → Ω → ℝ := fun i ω => -X i ω
  have hindepY : iIndepFun Y μ := by
    simpa [Y, Function.comp_def] using
      hindep.comp (fun _i x => -x) (fun _i => by fun_prop)
  have hsubY : ∀ i, HasSubgaussianMGF (Y i) ((1 / 2 : ℝ≥0) ^ 2) μ := by
    intro i
    apply (hsub i).neg.congr
    exact ae_of_all _ (fun _ω => rfl)
  have h := independent_table_scores_upper_tail μ Y hindepY hsubY heps
  simpa [Y] using h

/--
A direct fixed-pair RACE-style Hoeffding bound from raw independent table scores:
each table score is measurable, lies in `[0,1]`, and has the stated mean.
-/
theorem independent_bounded_table_scores_upper_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {L : ℕ} (Z : Fin L → Ω → ℝ) (mean : Fin L → ℝ)
    (hindep : iIndepFun Z μ)
    (hmeas : ∀ i, AEMeasurable (Z i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, Z i ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ i, ∫ ω, Z i ω ∂μ = mean i)
    {eps : ℝ} (heps : 0 ≤ eps) :
    μ.real {ω | eps ≤ ∑ i, (Z i ω - mean i)}
      ≤ Real.exp (-eps ^ 2 /
          (2 * (∑ _i : Fin L, ((1 / 2 : ℝ≥0) ^ 2) : ℝ≥0))) := by
  have hindep' := center_preserves_iIndepFun μ Z mean hindep
  have hsub : ∀ i,
      HasSubgaussianMGF (fun ω => Z i ω - mean i) ((1 / 2 : ℝ≥0) ^ 2) μ := by
    intro i
    exact centered_unit_interval_subgaussian μ (Z i) (mean i)
      (hmeas i) (hbound i) (hmean i)
  exact independent_table_scores_upper_tail μ
    (fun i ω => Z i ω - mean i) hindep' hsub heps

/-- Lower-tail companion to `independent_bounded_table_scores_upper_tail`. -/
theorem independent_bounded_table_scores_lower_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {L : ℕ} (Z : Fin L → Ω → ℝ) (mean : Fin L → ℝ)
    (hindep : iIndepFun Z μ)
    (hmeas : ∀ i, AEMeasurable (Z i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, Z i ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ i, ∫ ω, Z i ω ∂μ = mean i)
    {eps : ℝ} (heps : 0 ≤ eps) :
    μ.real {ω | eps ≤ -(∑ i, (Z i ω - mean i))}
      ≤ Real.exp (-eps ^ 2 /
          (2 * (∑ _i : Fin L, ((1 / 2 : ℝ≥0) ^ 2) : ℝ≥0))) := by
  have hindep' := center_preserves_iIndepFun μ Z mean hindep
  have hsub : ∀ i,
      HasSubgaussianMGF (fun ω => Z i ω - mean i) ((1 / 2 : ℝ≥0) ^ 2) μ := by
    intro i
    exact centered_unit_interval_subgaussian μ (Z i) (mean i)
      (hmeas i) (hbound i) (hmean i)
  exact independent_table_scores_lower_tail μ
    (fun i ω => Z i ω - mean i) hindep' hsub heps

end RACEFormal
