import RACEFormal.GaussianDirection
import Mathlib.Probability.Distributions.Gaussian.Fernique

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RACEFormal

/-- The product law of two independent standard Gaussian coordinates. -/
noncomputable def standardGaussianPlane : Measure (ℝ × ℝ) :=
  (gaussianReal 0 (1 : NNReal)).prod (gaussianReal 0 (1 : NNReal))

/-- The second hyperplane margin obtained by rotating the planar Gaussian by `alpha`. -/
noncomputable def rotatedGaussianMargin (alpha : ℝ) (z : ℝ × ℝ) : ℝ :=
  z.2 * Real.cos alpha - z.1 * Real.sin alpha

/-- The second coordinate of the standard Gaussian plane is itself standard Gaussian. -/
theorem hasLaw_standardGaussianPlane_snd :
    HasLaw (fun z : ℝ × ℝ => z.2) (gaussianReal 0 (1 : NNReal)) standardGaussianPlane := by
  refine ⟨by fun_prop, ?_⟩
  unfold standardGaussianPlane
  rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- A centered standard-Gaussian product measure is invariant under planar rotation. -/
theorem standardGaussianPlane_map_rotation (alpha : ℝ) :
    standardGaussianPlane.map (ContinuousLinearMap.rotation alpha) = standardGaussianPlane := by
  unfold standardGaussianPlane
  apply ProbabilityTheory.IsGaussian.map_rotation_eq_self
  simp

/--
The rotated hyperplane margin `z₂ cos(alpha) - z₁ sin(alpha)` is standard
Gaussian.  This is the distributional bridge needed to instantiate the
finite-temperature soft-RACE bias theorem on the same Gaussian plane used by
the exact angular collision calculation.
-/
theorem hasLaw_rotatedGaussianMargin (alpha : ℝ) :
    HasLaw (rotatedGaussianMargin alpha)
      (gaussianReal 0 (1 : NNReal)) standardGaussianPlane := by
  refine ⟨by
    unfold rotatedGaussianMargin
    fun_prop, ?_⟩
  have hcomp :
      rotatedGaussianMargin alpha =
        Prod.snd ∘ (ContinuousLinearMap.rotation alpha : ℝ × ℝ →L[ℝ] ℝ × ℝ) := by
    funext z
    simp only [rotatedGaussianMargin, Function.comp_apply,
      ContinuousLinearMap.rotation_apply, smul_eq_mul]
    ring
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    standardGaussianPlane_map_rotation alpha]
  unfold standardGaussianPlane
  rw [Measure.map_snd_prod, measure_univ, one_smul]

end RACEFormal
