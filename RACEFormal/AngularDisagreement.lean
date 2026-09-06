import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

open Set MeasureTheory

namespace RACEFormal

noncomputable section

/--
Inside the canonical angle representative interval `(-π, π]`, a rotation by
`alpha ∈ [0, π]` changes the sign of `sin` on two arcs, one on each side of
the cut.  These are the two real intervals whose total length is `2 * alpha`.
-/
def canonicalSignDisagreementIntervals (alpha : ℝ) : Set ℝ :=
  Set.Ioc 0 alpha ∪ Set.Ioc (-Real.pi) (alpha - Real.pi)

/-- The two canonical disagreement intervals are disjoint for `alpha ≤ π`. -/
theorem canonicalSignDisagreementIntervals_disjoint
    (alpha : ℝ) (hpi : alpha ≤ Real.pi) :
    Disjoint (Set.Ioc 0 alpha) (Set.Ioc (-Real.pi) (alpha - Real.pi)) := by
  refine Set.disjoint_left.2 fun x hx hy => ?_
  have hx0 : 0 < x := hx.1
  have hy0 : x ≤ alpha - Real.pi := hy.2
  have hcut : alpha - Real.pi ≤ 0 := sub_nonpos.mpr hpi
  linarith

/--
The canonical disagreement region has Lebesgue measure exactly `2 * alpha`.
This is the real-line measure calculation underlying the random-hyperplane
`alpha / π` sign-disagreement probability.
-/
theorem volume_canonicalSignDisagreementIntervals
    (alpha : ℝ) (h0 : 0 ≤ alpha) (hpi : alpha ≤ Real.pi) :
    volume (canonicalSignDisagreementIntervals alpha) =
      ENNReal.ofReal (2 * alpha) := by
  unfold canonicalSignDisagreementIntervals
  rw [measure_union (canonicalSignDisagreementIntervals_disjoint alpha hpi)
      measurableSet_Ioc]
  rw [Real.volume_Ioc, Real.volume_Ioc]
  have hsecond : alpha - Real.pi - -Real.pi = alpha := by ring
  rw [sub_zero, hsecond]
  rw [← ENNReal.ofReal_add h0 h0]
  congr 1
  ring

/--
The strict version removes the finitely many zero-sign boundary angles.  This
is the version that matches strict opposite signs exactly.
-/
def canonicalStrictSignDisagreementIntervals (alpha : ℝ) : Set ℝ :=
  Set.Ioo 0 alpha ∪ Set.Ioo (-Real.pi) (alpha - Real.pi)

/-- The two strict disagreement intervals are disjoint for `alpha ≤ π`. -/
theorem canonicalStrictSignDisagreementIntervals_disjoint
    (alpha : ℝ) (hpi : alpha ≤ Real.pi) :
    Disjoint (Set.Ioo 0 alpha) (Set.Ioo (-Real.pi) (alpha - Real.pi)) := by
  refine Set.disjoint_left.2 fun x hx hy => ?_
  have hx0 : 0 < x := hx.1
  have hy0 : x < alpha - Real.pi := hy.2
  have hcut : alpha - Real.pi ≤ 0 := sub_nonpos.mpr hpi
  linarith

/-- Removing the boundary points does not change the `2 * alpha` angular measure. -/
theorem volume_canonicalStrictSignDisagreementIntervals
    (alpha : ℝ) (h0 : 0 ≤ alpha) (hpi : alpha ≤ Real.pi) :
    volume (canonicalStrictSignDisagreementIntervals alpha) =
      ENNReal.ofReal (2 * alpha) := by
  unfold canonicalStrictSignDisagreementIntervals
  rw [measure_union (canonicalStrictSignDisagreementIntervals_disjoint alpha hpi)
      measurableSet_Ioo]
  rw [Real.volume_Ioo, Real.volume_Ioo]
  have hsecond : alpha - Real.pi - -Real.pi = alpha := by ring
  rw [sub_zero, hsecond]
  rw [← ENNReal.ofReal_add h0 h0]
  congr 1
  ring

/-- Normalizing the disagreement length by the full circle length gives `alpha / π`. -/
theorem normalized_angular_disagreement
    (alpha : ℝ) (h0 : 0 ≤ alpha) :
    (2 * alpha) / (2 * Real.pi) = alpha / Real.pi := by
  field_simp [Real.pi_ne_zero]

end

end RACEFormal
