import RACEFormal.Concentration
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace RACEFormal

/--
Two-sided Hoeffding bound for a fixed RACE query-key pair across independent
tables.  This packages the separate upper/lower tail lemmas into the absolute
error form used by the causal-triangle union bound.
-/
theorem independent_bounded_table_scores_two_sided
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {L : ℕ} (Z : Fin L → Ω → ℝ) (mean : Fin L → ℝ)
    (hindep : iIndepFun Z μ)
    (hmeas : ∀ i, AEMeasurable (Z i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, Z i ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ i, ∫ ω, Z i ω ∂μ = mean i)
    {eps : ℝ} (heps : 0 ≤ eps) :
    μ.real {ω | eps ≤ |∑ i, (Z i ω - mean i)|}
      ≤ 2 * Real.exp (-eps ^ 2 /
          (2 * (∑ _i : Fin L, ((1 / 2 : ℝ≥0) ^ 2) : ℝ≥0))) := by
  let S : Ω → ℝ := fun ω => ∑ i, (Z i ω - mean i)
  let q : ℝ := Real.exp (-eps ^ 2 /
    (2 * (∑ _i : Fin L, ((1 / 2 : ℝ≥0) ^ 2) : ℝ≥0)))
  have hupper : μ.real {ω | eps ≤ S ω} ≤ q := by
    simpa [S, q] using
      independent_bounded_table_scores_upper_tail μ Z mean hindep hmeas hbound hmean heps
  have hlower : μ.real {ω | eps ≤ -(S ω)} ≤ q := by
    simpa [S, q] using
      independent_bounded_table_scores_lower_tail μ Z mean hindep hmeas hbound hmean heps
  have hsubset :
      {ω | eps ≤ |S ω|} ⊆ {ω | eps ≤ S ω} ∪ {ω | eps ≤ -(S ω)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    by_cases hs : 0 ≤ S ω
    · left
      simpa [abs_of_nonneg hs] using hω
    · right
      have hs' : S ω ≤ 0 := le_of_not_ge hs
      simpa [abs_of_nonpos hs'] using hω
  calc
    μ.real {ω | eps ≤ |∑ i, (Z i ω - mean i)|}
        = μ.real {ω | eps ≤ |S ω|} := by rfl
    _ ≤ μ.real ({ω | eps ≤ S ω} ∪ {ω | eps ≤ -(S ω)}) :=
      measureReal_mono hsubset
    _ ≤ μ.real {ω | eps ≤ S ω} + μ.real {ω | eps ≤ -(S ω)} :=
      measureReal_union_le _ _
    _ ≤ q + q := add_le_add hupper hlower
    _ = 2 * Real.exp (-eps ^ 2 /
          (2 * (∑ _i : Fin L, ((1 / 2 : ℝ≥0) ^ 2) : ℝ≥0))) := by
      dsimp [q]
      ring

end RACEFormal
