import RACEFormal.GaussianRadial
import Mathlib.MeasureTheory.Integral.Prod

open Set MeasureTheory
open ProbabilityTheory
open scoped ENNReal NNReal

namespace RACEFormal

noncomputable section

/-- The ordinary real-valued density of two independent standard Gaussian coordinates. -/
def standardGaussianPlaneDensityReal (z : ℝ × ℝ) : ℝ :=
  gaussianPDFReal 0 (1 : NNReal) z.1 * gaussianPDFReal 0 (1 : NNReal) z.2

/-- The `ENNReal` density used by `withDensity` for the standard Gaussian plane. -/
def standardGaussianPlaneDensity (z : ℝ × ℝ) : ENNReal :=
  gaussianPDF 0 (1 : NNReal) z.1 * gaussianPDF 0 (1 : NNReal) z.2

@[fun_prop]
theorem measurable_standardGaussianPlaneDensity : Measurable standardGaussianPlaneDensity := by
  unfold standardGaussianPlaneDensity
  fun_prop

theorem standardGaussianPlaneDensity_lt_top (z : ℝ × ℝ) :
    standardGaussianPlaneDensity z < ∞ := by
  unfold standardGaussianPlaneDensity
  exact ENNReal.mul_lt_top gaussianPDF_lt_top gaussianPDF_lt_top

@[simp]
theorem toReal_standardGaussianPlaneDensity (z : ℝ × ℝ) :
    (standardGaussianPlaneDensity z).toReal = standardGaussianPlaneDensityReal z := by
  simp [standardGaussianPlaneDensity, standardGaussianPlaneDensityReal]

/-- The product-Gaussian measure written with the named planar density. -/
theorem standardGaussianPlane_eq_withDensity_named :
    (gaussianReal 0 (1 : NNReal)).prod (gaussianReal 0 (1 : NNReal)) =
      ((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
        standardGaussianPlaneDensity := by
  change
    (gaussianReal 0 (1 : NNReal)).prod (gaussianReal 0 (1 : NNReal)) =
      ((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
        (fun z : ℝ × ℝ => gaussianPDF 0 (1 : NNReal) z.1 * gaussianPDF 0 (1 : NNReal) z.2)
  exact standardGaussianPlane_eq_withDensity

/-- In polar coordinates the real planar Gaussian density depends only on the radius. -/
theorem standardGaussianPlaneDensityReal_polar (r theta : ℝ) :
    standardGaussianPlaneDensityReal (polarCoord.symm (r, theta)) =
      (2 * Real.pi)⁻¹ * Real.exp (-(r ^ 2) / 2) := by
  simpa [standardGaussianPlaneDensityReal] using gaussianPDFReal_polar_product r theta

/-- The canonical strict angular region has real Lebesgue integral `2 * alpha`. -/
theorem integral_one_canonicalStrictSignDisagreementIntervals
    (alpha : ℝ) (ha0 : 0 < alpha) (hapi : alpha < Real.pi) :
    (∫ _theta in canonicalStrictSignDisagreementIntervals alpha, (1 : ℝ)) =
      2 * alpha := by
  simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
    Set.univ_inter, smul_eq_mul, mul_one]
  rw [Measure.real,
    volume_canonicalStrictSignDisagreementIntervals alpha ha0.le hapi.le,
    ENNReal.toReal_ofReal]
  positivity

/--
The two-dimensional standard-Gaussian density assigns mass exactly `alpha / π`
to the strict disagreement wedge for two hyperplanes separated by `alpha`.
-/
theorem integral_standardGaussianPlaneDensityReal_disagreement
    (alpha : ℝ) (ha0 : 0 < alpha) (hapi : alpha < Real.pi) :
    (∫ z in gaussianPlaneDisagreement alpha, standardGaussianPlaneDensityReal z) =
      alpha / Real.pi := by
  have hD : MeasurableSet (gaussianPlaneDisagreement alpha) :=
    measurableSet_gaussianPlaneDisagreement alpha
  have hpre : MeasurableSet
      (polarCoord.symm ⁻¹' gaussianPlaneDisagreement alpha) :=
    hD.preimage continuous_polarCoord_symm.measurable
  have hcanon : MeasurableSet (canonicalStrictSignDisagreementIntervals alpha) := by
    exact measurableSet_Ioo.union measurableSet_Ioo
  have hset :
      polarCoord.target ∩ (polarCoord.symm ⁻¹' gaussianPlaneDisagreement alpha) =
        Set.Ioi (0 : ℝ) ×ˢ canonicalStrictSignDisagreementIntervals alpha := by
    ext p
    change (p ∈ polarCoord.target ∧
      polarCoord.symm p ∈ gaussianPlaneDisagreement alpha) ↔
        p ∈ Set.Ioi (0 : ℝ) ×ˢ canonicalStrictSignDisagreementIntervals alpha
    exact Set.ext_iff.mp (polar_target_disagreement_preimage alpha ha0 hapi) p
  calc
    (∫ z in gaussianPlaneDisagreement alpha, standardGaussianPlaneDensityReal z)
        = ∫ z, (gaussianPlaneDisagreement alpha).indicator
            standardGaussianPlaneDensityReal z := by
              rw [integral_indicator hD]
    _ = ∫ p in polarCoord.target,
          p.1 * ((gaussianPlaneDisagreement alpha).indicator
            standardGaussianPlaneDensityReal (polarCoord.symm p)) := by
          simpa only [smul_eq_mul] using
            (integral_comp_polarCoord_symm
              ((gaussianPlaneDisagreement alpha).indicator
                standardGaussianPlaneDensityReal)).symm
    _ = ∫ p in polarCoord.target,
          (polarCoord.symm ⁻¹' gaussianPlaneDisagreement alpha).indicator
            (fun p => p.1 * standardGaussianPlaneDensityReal (polarCoord.symm p)) p := by
          apply setIntegral_congr_fun polarCoord.open_target.measurableSet
          intro p _hp
          change
            p.1 * (gaussianPlaneDisagreement alpha).indicator standardGaussianPlaneDensityReal
                (polarCoord.symm p) =
              (polarCoord.symm ⁻¹' gaussianPlaneDisagreement alpha).indicator
                (fun q => q.1 * standardGaussianPlaneDensityReal (polarCoord.symm q)) p
          by_cases h : polarCoord.symm p ∈ gaussianPlaneDisagreement alpha
          · have hp : p ∈ polarCoord.symm ⁻¹' gaussianPlaneDisagreement alpha := h
            rw [Set.indicator_of_mem h, Set.indicator_of_mem hp]
          · have hp : p ∉ polarCoord.symm ⁻¹' gaussianPlaneDisagreement alpha := h
            rw [Set.indicator_of_notMem h, Set.indicator_of_notMem hp]
            simp
    _ = ∫ p in polarCoord.target ∩
          (polarCoord.symm ⁻¹' gaussianPlaneDisagreement alpha),
          p.1 * standardGaussianPlaneDensityReal (polarCoord.symm p) := by
          rw [setIntegral_indicator hpre]
    _ = ∫ p in Set.Ioi (0 : ℝ) ×ˢ canonicalStrictSignDisagreementIntervals alpha,
          p.1 * standardGaussianPlaneDensityReal (polarCoord.symm p) := by
          rw [hset]
    _ = ∫ p in Set.Ioi (0 : ℝ) ×ˢ canonicalStrictSignDisagreementIntervals alpha,
          (p.1 * ((2 * Real.pi)⁻¹ * Real.exp (-(p.1 ^ 2) / 2))) * (1 : ℝ) := by
          apply setIntegral_congr_fun (measurableSet_Ioi.prod hcanon)
          rintro ⟨r, theta⟩ _hp
          change
            r * standardGaussianPlaneDensityReal (polarCoord.symm (r, theta)) =
              (r * ((2 * Real.pi)⁻¹ * Real.exp (-(r ^ 2) / 2))) * (1 : ℝ)
          rw [standardGaussianPlaneDensityReal_polar]
          ring
    _ = (∫ r in Set.Ioi (0 : ℝ),
            r * ((2 * Real.pi)⁻¹ * Real.exp (-(r ^ 2) / 2))) *
          (∫ theta in canonicalStrictSignDisagreementIntervals alpha, (1 : ℝ)) := by
          rw [Measure.volume_eq_prod]
          exact
            setIntegral_prod_mul
              (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
              (fun r : ℝ => r * ((2 * Real.pi)⁻¹ * Real.exp (-(r ^ 2) / 2)))
              (fun _theta : ℝ => (1 : ℝ))
              (Set.Ioi (0 : ℝ)) (canonicalStrictSignDisagreementIntervals alpha)
    _ = (2 * Real.pi)⁻¹ * (2 * alpha) := by
          rw [integral_standard_gaussian_radial_density,
            integral_one_canonicalStrictSignDisagreementIntervals alpha ha0 hapi]
    _ = alpha / Real.pi := by
          field_simp [Real.pi_ne_zero]

/--
For two independent standard Gaussian coordinates, the strict random-hyperplane
sign-disagreement event has probability exactly `alpha / π`.
-/
theorem standardGaussianPlane_disagreement_probability
    (alpha : ℝ) (ha0 : 0 < alpha) (hapi : alpha < Real.pi) :
    ((gaussianReal 0 (1 : NNReal)).prod (gaussianReal 0 (1 : NNReal))).real
        (gaussianPlaneDisagreement alpha) = alpha / Real.pi := by
  have hD : MeasurableSet (gaussianPlaneDisagreement alpha) :=
    measurableSet_gaussianPlaneDisagreement alpha
  calc
    ((gaussianReal 0 (1 : NNReal)).prod (gaussianReal 0 (1 : NNReal))).real
        (gaussianPlaneDisagreement alpha)
        = ∫ z in gaussianPlaneDisagreement alpha, (1 : ℝ)
            ∂((gaussianReal 0 (1 : NNReal)).prod (gaussianReal 0 (1 : NNReal))) := by
              simp
    _ = ∫ z, (gaussianPlaneDisagreement alpha).indicator (fun _ => (1 : ℝ)) z
            ∂((gaussianReal 0 (1 : NNReal)).prod (gaussianReal 0 (1 : NNReal))) := by
              rw [integral_indicator hD]
    _ = ∫ z, (standardGaussianPlaneDensity z).toReal •
            (gaussianPlaneDisagreement alpha).indicator (fun _ => (1 : ℝ)) z
            ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
              rw [standardGaussianPlane_eq_withDensity_named,
                integral_withDensity_eq_integral_toReal_smul
                  measurable_standardGaussianPlaneDensity
                  (ae_of_all _ standardGaussianPlaneDensity_lt_top)]
    _ = ∫ z, (gaussianPlaneDisagreement alpha).indicator
            standardGaussianPlaneDensityReal z
            ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
              apply integral_congr_ae
              exact ae_of_all _ fun z => by
                by_cases hz : z ∈ gaussianPlaneDisagreement alpha
                · simp [hz, smul_eq_mul]
                · simp [hz]
    _ = ∫ z in gaussianPlaneDisagreement alpha, standardGaussianPlaneDensityReal z
            ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
              rw [integral_indicator hD]
    _ = alpha / Real.pi := by
              simpa [Measure.volume_eq_prod] using
                integral_standardGaussianPlaneDensityReal_disagreement alpha ha0 hapi

end

end RACEFormal
