import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory
open scoped BigOperators

namespace RACEFormal

/-- Finite union bound written for real-valued measures. -/
theorem finite_failure_union_bound
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (bad : I → Set Ω) :
    μ.real (⋃ i, bad i) ≤ ∑ i, μ.real (bad i) := by
  exact measureReal_iUnion_fintype_le bad

/--
If every member of a finite family has failure probability at most `q`, the
probability that any member fails is at most `card(I) * q`.
This is the abstract simultaneous-concentration step used for the causal triangle.
-/
theorem finite_failure_union_bound_uniform
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (bad : I → Set Ω) (q : ℝ)
    (hbad : ∀ i, μ.real (bad i) ≤ q) :
    μ.real (⋃ i, bad i) ≤ (Fintype.card I : ℝ) * q := by
  calc
    μ.real (⋃ i, bad i) ≤ ∑ i, μ.real (bad i) :=
      finite_failure_union_bound μ bad
    _ ≤ ∑ _i : I, q := by
      exact Finset.sum_le_sum fun i _hi => hbad i
    _ = (Fintype.card I : ℝ) * q := by simp

end RACEFormal
