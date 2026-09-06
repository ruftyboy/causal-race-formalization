import RACEFormal.GaussianDirection
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Gamma

open Set MeasureTheory
open ProbabilityTheory

namespace RACEFormal

noncomputable section

/-- The product of two independent standard Gaussian measures is the product Lebesgue
measure with density equal to the product of the two one-dimensional Gaussian pdfs. -/
theorem standardGaussianPlane_eq_withDensity :
    (gaussianReal 0 (1 : NNReal)).prod (gaussianReal 0 (1 : NNReal)) =
      ((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
        (fun z : ℝ × ℝ => gaussianPDF 0 (1 : NNReal) z.1 * gaussianPDF 0 (1 : NNReal) z.2) := by
  rw [gaussianReal_of_var_ne_zero 0 (v := (1 : NNReal)) one_ne_zero]
  exact MeasureTheory.prod_withDensity
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (f := gaussianPDF 0 (1 : NNReal)) (g := gaussianPDF 0 (1 : NNReal))
    (measurable_gaussianPDF 0 (1 : NNReal)) (measurable_gaussianPDF 0 (1 : NNReal))

/-- In polar coordinates, the product of two standard real Gaussian densities is radial. -/
theorem gaussianPDFReal_polar_product (r theta : ℝ) :
    gaussianPDFReal 0 1 (r * Real.cos theta) *
        gaussianPDFReal 0 1 (r * Real.sin theta) =
      (2 * Real.pi)⁻¹ * Real.exp (-(r ^ 2) / 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have hsq :
      (r * Real.cos theta) ^ 2 + (r * Real.sin theta) ^ 2 = r ^ 2 := by
    calc
      (r * Real.cos theta) ^ 2 + (r * Real.sin theta) ^ 2
          = r ^ 2 * (Real.cos theta ^ 2 + Real.sin theta ^ 2) := by ring
      _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]
  have hsqrt : (Real.sqrt (2 * Real.pi)) ^ 2 = 2 * Real.pi := by
    rw [Real.sq_sqrt]
    positivity
  have hc :
      (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹ =
        (2 * Real.pi)⁻¹ := by
    rw [← mul_inv_rev, ← sq, hsqrt]
  have hexp :
      -(r * Real.cos theta) ^ 2 / 2 + -(r * Real.sin theta) ^ 2 / 2 =
        -(r ^ 2) / 2 := by
    linarith
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(r * Real.cos theta) ^ 2 / 2) *
          ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(r * Real.sin theta) ^ 2 / 2))
        = ((Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹) *
            (Real.exp (-(r * Real.cos theta) ^ 2 / 2) *
              Real.exp (-(r * Real.sin theta) ^ 2 / 2)) := by ring
    _ = ((Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹) *
          Real.exp (-(r * Real.cos theta) ^ 2 / 2 +
            -(r * Real.sin theta) ^ 2 / 2) := by
      rw [Real.exp_add]
    _ = (2 * Real.pi)⁻¹ * Real.exp (-(r ^ 2) / 2) := by
      rw [hc, hexp]

/-- The unnormalised radial kernel `r exp(-r²/2)` integrates to one on the positive ray. -/
theorem integral_standard_gaussian_radial_kernel :
    (∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-(r ^ 2) / 2)) = 1 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (1 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [Real.rpow_one, Real.rpow_two, Real.rpow_neg_one, Real.Gamma_one] at h
  convert h using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _hr
  ring_nf

/-- The normalized radial part of the planar standard-Gaussian density integrates to `1/(2π)`. -/
theorem integral_standard_gaussian_radial_density :
    (∫ r in Set.Ioi (0 : ℝ),
      r * ((2 * Real.pi)⁻¹ * Real.exp (-(r ^ 2) / 2))) =
      (2 * Real.pi)⁻¹ := by
  calc
    (∫ r in Set.Ioi (0 : ℝ),
      r * ((2 * Real.pi)⁻¹ * Real.exp (-(r ^ 2) / 2))) =
        (2 * Real.pi)⁻¹ *
          (∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-(r ^ 2) / 2)) := by
            rw [← integral_const_mul]
            apply setIntegral_congr_fun measurableSet_Ioi
            intro r _hr
            ring
    _ = (2 * Real.pi)⁻¹ := by
      rw [integral_standard_gaussian_radial_kernel]
      ring

/-- The radial standard-Gaussian density is integrable on the positive ray. -/
theorem integrableOn_standard_gaussian_radial_density :
    IntegrableOn
      (fun r : ℝ => r * ((2 * Real.pi)⁻¹ * Real.exp (-(r ^ 2) / 2)))
      (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (1 : ℝ)) (p := (2 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have hk0 : IntegrableOn
      (fun r : ℝ => r * Real.exp (-(1 / 2 : ℝ) * r ^ 2)) (Set.Ioi 0) := by
    simpa [Real.rpow_one, Real.rpow_two, pow_one] using h
  have hk : IntegrableOn
      (fun r : ℝ => r * Real.exp (-(r ^ 2) / 2)) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun hk0 ?_ measurableSet_Ioi
    intro r _hr
    ring_nf
  have hc : IntegrableOn
      (fun r : ℝ => (2 * Real.pi)⁻¹ *
        (r * Real.exp (-(r ^ 2) / 2))) (Set.Ioi 0) :=
    hk.const_mul ((2 * Real.pi)⁻¹)
  refine IntegrableOn.congr_fun hc ?_ measurableSet_Ioi
  intro r _hr
  ring

/-- ENNReal form of the exact radial normalization, convenient for Tonelli/polar-coordinate proofs. -/
theorem lintegral_standard_gaussian_radial_density :
    (∫⁻ r in Set.Ioi (0 : ℝ),
      ENNReal.ofReal
        (r * ((2 * Real.pi)⁻¹ * Real.exp (-(r ^ 2) / 2)))) =
      ENNReal.ofReal ((2 * Real.pi)⁻¹) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · exact congrArg ENNReal.ofReal integral_standard_gaussian_radial_density
  · exact integrableOn_standard_gaussian_radial_density
  · exact ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => by
      have hr0 : 0 ≤ r := (Set.mem_Ioi.mp hr).le
      positivity)

end

end RACEFormal
