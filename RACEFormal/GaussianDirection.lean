import RACEFormal.RandomHyperplaneCollision
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Probability.Distributions.Gaussian.Real

open Set MeasureTheory

namespace RACEFormal

noncomputable section

/--
The two-dimensional strict sign-disagreement event corresponding to two
hyperplanes separated by angle `alpha`.  In polar coordinates its two linear
forms are proportional to `sin theta` and `sin (theta - alpha)`.
-/
def gaussianPlaneDisagreement (alpha : ℝ) : Set (ℝ × ℝ) :=
  {z |
    (0 < z.2 ∧ z.2 * Real.cos alpha - z.1 * Real.sin alpha < 0) ∨
    (z.2 < 0 ∧ 0 < z.2 * Real.cos alpha - z.1 * Real.sin alpha)}

/-- The planar disagreement wedge is an open, hence measurable, subset of `ℝ²`. -/
theorem measurableSet_gaussianPlaneDisagreement (alpha : ℝ) :
    MeasurableSet (gaussianPlaneDisagreement alpha) := by
  have hy : Continuous (fun z : ℝ × ℝ => z.2) := continuous_snd
  have hlin : Continuous (fun z : ℝ × ℝ =>
      z.2 * Real.cos alpha - z.1 * Real.sin alpha) :=
    (continuous_snd.mul continuous_const).sub (continuous_fst.mul continuous_const)
  unfold gaussianPlaneDisagreement
  exact (((isOpen_lt continuous_const hy).inter (isOpen_lt hlin continuous_const)).union
    ((isOpen_lt hy continuous_const).inter (isOpen_lt continuous_const hlin))).measurableSet

/--
For positive radius, pulling the planar wedge back through polar coordinates
produces exactly the pair of strict sine-sign inequalities.
-/
theorem polar_symm_mem_gaussianPlaneDisagreement_iff
    (alpha r theta : ℝ) (hr : 0 < r) :
    polarCoord.symm (r, theta) ∈ gaussianPlaneDisagreement alpha ↔
      ((0 < Real.sin theta ∧ Real.sin (theta - alpha) < 0) ∨
        (Real.sin theta < 0 ∧ 0 < Real.sin (theta - alpha))) := by
  change
    ((0 < r * Real.sin theta ∧
        r * Real.sin theta * Real.cos alpha -
            r * Real.cos theta * Real.sin alpha < 0) ∨
      (r * Real.sin theta < 0 ∧
        0 < r * Real.sin theta * Real.cos alpha -
            r * Real.cos theta * Real.sin alpha)) ↔ _
  have htrig :
      r * Real.sin theta * Real.cos alpha -
          r * Real.cos theta * Real.sin alpha =
        r * Real.sin (theta - alpha) := by
    rw [Real.sin_sub]
    ring
  have hpos (x : ℝ) : 0 < r * x ↔ 0 < x := by
    constructor
    · intro h
      by_contra hnot
      have hx : x ≤ 0 := le_of_not_gt hnot
      have : r * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr.le hx
      linarith
    · exact fun hx => mul_pos hr hx
  have hneg (x : ℝ) : r * x < 0 ↔ x < 0 := by
    constructor
    · intro h
      by_contra hnot
      have hx : 0 ≤ x := le_of_not_gt hnot
      have : 0 ≤ r * x := mul_nonneg hr.le hx
      linarith
    · exact fun hx => mul_neg_of_pos_of_neg hr hx
  rw [htrig]
  simp only [hpos, hneg]

/-- Strict canonical disagreement arcs lie in the open angular representative interval. -/
theorem canonicalStrictSignDisagreementIntervals_subset_Ioo_circle
    (alpha : ℝ) (hapi : alpha < Real.pi) :
    canonicalStrictSignDisagreementIntervals alpha ⊆
      Set.Ioo (-Real.pi) Real.pi := by
  intro x hx
  simp only [canonicalStrictSignDisagreementIntervals, Set.mem_union,
    Set.mem_Ioo] at hx
  rcases hx with hx | hx
  · constructor
    · linarith [Real.pi_pos, hx.1]
    · linarith [hx.2, hapi]
  · constructor
    · exact hx.1
    · linarith [hx.2, hapi, Real.pi_pos]

/--
Inside the polar-coordinate target `(0,∞) × (-π,π)`, the planar disagreement
wedge is precisely positive radius times the canonical angular disagreement arcs.
-/
theorem polar_target_disagreement_preimage
    (alpha : ℝ) (ha0 : 0 < alpha) (hapi : alpha < Real.pi) :
    {p : ℝ × ℝ | p ∈ polarCoord.target ∧
        polarCoord.symm p ∈ gaussianPlaneDisagreement alpha} =
      Set.Ioi (0 : ℝ) ×ˢ canonicalStrictSignDisagreementIntervals alpha := by
  ext p
  rcases p with ⟨r, theta⟩
  simp only [polarCoord_target, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Ioi,
    Set.mem_Ioo]
  constructor
  · rintro ⟨⟨hr, htheta⟩, hdis⟩
    refine ⟨hr, ?_⟩
    exact (real_strict_circle_sine_disagreement_iff alpha theta ha0 hapi
      ⟨htheta.1, htheta.2.le⟩).1
      ((polar_symm_mem_gaussianPlaneDisagreement_iff alpha r theta hr).1 hdis)
  · rintro ⟨hr, hcanon⟩
    have hthetaOpen :=
      canonicalStrictSignDisagreementIntervals_subset_Ioo_circle alpha hapi hcanon
    refine ⟨⟨hr, hthetaOpen⟩, ?_⟩
    apply (polar_symm_mem_gaussianPlaneDisagreement_iff alpha r theta hr).2
    exact (real_strict_circle_sine_disagreement_iff alpha theta ha0 hapi
      ⟨hthetaOpen.1, hthetaOpen.2.le⟩).2 hcanon

end

end RACEFormal
