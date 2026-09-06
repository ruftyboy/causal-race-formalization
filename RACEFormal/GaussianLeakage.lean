import Mathlib

open Set MeasureTheory

namespace RACEFormal

/-- Monotonicity of the real hyperbolic tangent, obtained from the formal inverse `artanh`. -/
theorem tanh_monotone : Monotone Real.tanh := by
  intro x y hxy
  have hx : Real.tanh x ∈ Ioo (-1 : ℝ) 1 :=
    ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩
  have hy : Real.tanh y ∈ Ioo (-1 : ℝ) 1 :=
    ⟨Real.neg_one_lt_tanh y, Real.tanh_lt_one y⟩
  apply (Real.artanh_le_artanh_iff hx hy).mp
  simpa only [Real.artanh_tanh] using hxy

/--
On `[0,1]`, `artanh (x/2) ≤ x`.  This elementary estimate is the convenient
inverse-function form of the lower bound `x/2 ≤ tanh x` used in the RACE
finite-temperature bias argument.
-/
theorem artanh_half_le_self {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.artanh (x / 2) ≤ x := by
  have hy : x / 2 ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith
  rw [Real.artanh_eq_half_log hy]
  have hden : 0 < 1 - x / 2 := by linarith
  have hnum : 0 < 1 + x / 2 := by linarith
  have hratio : 0 < (1 + x / 2) / (1 - x / 2) := div_pos hnum hden
  have hlog := Real.log_le_sub_one_of_pos hratio
  have h2x : (2 : ℝ) - x ≠ 0 := by linarith
  have hrsub :
      (1 + x / 2) / (1 - x / 2) - 1 = x / (1 - x / 2) := by
    field_simp [h2x]
    ring
  have hfrac : (1 / 2 : ℝ) * (x / (1 - x / 2)) ≤ x := by
    rw [show (1 / 2 : ℝ) * (x / (1 - x / 2)) =
      (x / 2) / (1 - x / 2) by ring]
    rw [div_le_iff₀ hden]
    have hprod : 0 ≤ x * (1 - x) :=
      mul_nonneg hx0 (sub_nonneg.mpr hx1)
    nlinarith
  calc
    (1 / 2 : ℝ) * Real.log ((1 + x / 2) / (1 - x / 2))
        ≤ (1 / 2 : ℝ) * ((1 + x / 2) / (1 - x / 2) - 1) := by
          exact mul_le_mul_of_nonneg_left hlog (by norm_num)
    _ = (1 / 2 : ℝ) * (x / (1 - x / 2)) := by rw [hrsub]
    _ ≤ x := hfrac

/-- The local linear lower bound `x/2 ≤ tanh x` for `0 ≤ x ≤ 1`. -/
theorem half_le_tanh_on_unit {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ Real.tanh x := by
  have hxhalf : x / 2 ∈ Ioo (-1 : ℝ) 1 := by
    constructor <;> linarith
  have htanh : Real.tanh x ∈ Ioo (-1 : ℝ) 1 :=
    ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩
  apply (Real.artanh_le_artanh_iff hxhalf htanh).mp
  simpa only [Real.artanh_tanh] using artanh_half_le_self hx0 hx1

/-- Absolute-value compatibility of `tanh`: `|tanh z| = tanh |z|`. -/
theorem abs_tanh_eq_tanh_abs (z : ℝ) :
    |Real.tanh z| = Real.tanh |z| := by
  by_cases hz : 0 ≤ z
  · have htz : 0 ≤ Real.tanh z := by
      simpa using (tanh_monotone hz)
    rw [abs_of_nonneg hz, abs_of_nonneg htz]
  · have hzlt : z < 0 := lt_of_not_ge hz
    have htz : Real.tanh z ≤ 0 := by
      simpa using (tanh_monotone (le_of_lt hzlt))
    rw [abs_of_neg hzlt, abs_of_nonpos htz, Real.tanh_neg]

/-- Near the hyperplane, `|tanh z|` is at least half of `|z|`. -/
theorem half_abs_le_abs_tanh_of_abs_le_one {z : ℝ} (hz : |z| ≤ 1) :
    |z| / 2 ≤ |Real.tanh z| := by
  rw [abs_tanh_eq_tanh_abs]
  exact half_le_tanh_on_unit (abs_nonneg z) hz

/-- Away from the hyperplane, `|tanh z|` is at least `tanh 1`. -/
theorem tanh_one_le_abs_tanh_of_one_le_abs {z : ℝ} (hz : 1 ≤ |z|) :
    Real.tanh 1 ≤ |Real.tanh z| := by
  rw [abs_tanh_eq_tanh_abs]
  exact tanh_monotone hz

/--
Pointwise split used to integrate the soft RACE leakage against a standard
Gaussian.  Inside `|z| ≤ 1` the decay is at least `exp (-β|z|)`; outside that
strip it is at most the constant `exp (-2β tanh(1))`.
-/
theorem gaussian_leakage_pointwise_split
    (beta z : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-2 * beta * |Real.tanh z|) ≤
      if |z| ≤ 1 then Real.exp (-beta * |z|)
      else Real.exp (-2 * beta * Real.tanh 1) := by
  by_cases hz : |z| ≤ 1
  · rw [if_pos hz]
    apply Real.exp_le_exp.mpr
    have hlocal := half_abs_le_abs_tanh_of_abs_le_one hz
    have hmul := mul_le_mul_of_nonneg_left hlocal
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hbeta)
    nlinarith
  · rw [if_neg hz]
    apply Real.exp_le_exp.mpr
    have hzfar : 1 ≤ |z| := le_of_lt (lt_of_not_ge hz)
    have hfar := tanh_one_le_abs_tanh_of_one_le_abs hzfar
    have hmul := mul_le_mul_of_nonneg_left hfar
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hbeta)
    nlinarith

/-- A branch-free envelope convenient for taking expectations. -/
theorem gaussian_leakage_sum_envelope
    (beta z : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-2 * beta * |Real.tanh z|) ≤
      Real.exp (-beta * |z|) + Real.exp (-2 * beta * Real.tanh 1) := by
  have h := gaussian_leakage_pointwise_split beta z hbeta
  by_cases hz : |z| ≤ 1
  · rw [if_pos hz] at h
    exact h.trans (le_add_of_nonneg_right (Real.exp_nonneg _))
  · rw [if_neg hz] at h
    exact h.trans (le_add_of_nonneg_left (Real.exp_nonneg _))

/-- The Laplace envelope `exp (-β |x|)` is integrable on the real line for `β > 0`. -/
theorem integrable_exp_neg_mul_abs (beta : ℝ) (hbeta : 0 < beta) :
    Integrable (fun x : ℝ => Real.exp (-beta * |x|)) := by
  have hleft0 : IntegrableOn (fun x : ℝ => Real.exp (beta * x)) (Iic 0) :=
    integrableOn_exp_mul_Iic hbeta 0
  have hleft : IntegrableOn (fun x : ℝ => Real.exp (-beta * |x|)) (Iic 0) := by
    refine IntegrableOn.congr_fun hleft0 ?_ measurableSet_Iic
    intro x hx
    have hx0 : x ≤ 0 := mem_Iic.mp hx
    change Real.exp (beta * x) = Real.exp (-beta * |x|)
    rw [abs_of_nonpos hx0]
    congr 1
    ring
  have hright0 : IntegrableOn (fun x : ℝ => Real.exp ((-beta) * x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hright : IntegrableOn (fun x : ℝ => Real.exp (-beta * |x|)) (Ioi 0) := by
    refine IntegrableOn.congr_fun hright0 ?_ measurableSet_Ioi
    intro x hx
    have hx0 : 0 ≤ x := (mem_Ioi.mp hx).le
    change Real.exp (-beta * x) = Real.exp (-beta * |x|)
    rw [abs_of_nonneg hx0]
  have hunion := hleft.union hright
  simpa only [Iic_union_Ioi, integrableOn_univ] using hunion

/-- Exact integral of the Laplace envelope. -/
theorem integral_exp_neg_mul_abs (beta : ℝ) (hbeta : 0 < beta) :
    (∫ x : ℝ, Real.exp (-beta * |x|)) = 2 / beta := by
  calc
    (∫ x : ℝ, Real.exp (-beta * |x|))
        = 2 * ∫ x : ℝ in Ioi (0 : ℝ), Real.exp (-beta * x) := by
            simpa only using
              (integral_comp_abs (f := fun x : ℝ => Real.exp (-beta * x)))
    _ = 2 / beta := by
      rw [integral_exp_mul_Ioi (a := -beta) (by linarith) 0]
      simp [div_eq_mul_inv]

/-- The standard normal density never exceeds its value at the origin. -/
theorem standard_gaussian_pdf_le_peak (x : ℝ) :
    ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x ≤
      (Real.sqrt (2 * Real.pi))⁻¹ := by
  rw [ProbabilityTheory.gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have hcoef : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  have hexp : Real.exp (-x ^ 2 / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg x]
  simpa using mul_le_mul_of_nonneg_left hexp hcoef

/-- The standard Gaussian density times the Laplace envelope is integrable. -/
theorem integrable_standard_gaussian_mul_laplace
    (beta : ℝ) (hbeta : 0 < beta) :
    Integrable (fun x : ℝ =>
      ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x *
        Real.exp (-beta * |x|)) := by
  refine (integrable_exp_neg_mul_abs beta hbeta).bdd_mul
    (c := (Real.sqrt (2 * Real.pi))⁻¹) (by fun_prop) ?_
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (ProbabilityTheory.gaussianPDFReal_nonneg 0 (1 : NNReal) x)]
    exact standard_gaussian_pdf_le_peak x

/-- The Gaussian-weighted Laplace envelope is bounded by peak-density times `2 / β`. -/
theorem standard_gaussian_laplace_integral_le_peak
    (beta : ℝ) (hbeta : 0 < beta) :
    (∫ x : ℝ,
      ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x *
        Real.exp (-beta * |x|)) ≤
      (Real.sqrt (2 * Real.pi))⁻¹ * (2 / beta) := by
  calc
    (∫ x : ℝ,
      ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x *
        Real.exp (-beta * |x|))
        ≤ ∫ x : ℝ,
            (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-beta * |x|) := by
          apply integral_mono_of_nonneg
          · exact ae_of_all _ fun x =>
              mul_nonneg
                (ProbabilityTheory.gaussianPDFReal_nonneg 0 (1 : NNReal) x)
                (Real.exp_nonneg _)
          · exact (integrable_exp_neg_mul_abs beta hbeta).const_mul _
          · exact ae_of_all _ fun x =>
              mul_le_mul_of_nonneg_right
                (standard_gaussian_pdf_le_peak x) (Real.exp_nonneg _)
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
        (∫ x : ℝ, Real.exp (-beta * |x|)) := by
          rw [integral_const_mul]
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * (2 / beta) := by
          rw [integral_exp_neg_mul_abs beta hbeta]

/--
For a standard Gaussian margin, the finite-temperature leakage envelope has
expectation at most `2/(sqrt(2π) β) + exp(-2 β tanh(1))`.
-/
theorem standard_gaussian_leakage_expectation_bound
    (beta : ℝ) (hbeta : 0 < beta) :
    (∫ z : ℝ, Real.exp (-2 * beta * |Real.tanh z|)
      ∂(ProbabilityTheory.gaussianReal 0 (1 : NNReal))) ≤
      (Real.sqrt (2 * Real.pi))⁻¹ * (2 / beta) +
        Real.exp (-2 * beta * Real.tanh 1) := by
  have hone : (1 : NNReal) ≠ 0 := one_ne_zero
  have hchange :
      (∫ z : ℝ, Real.exp (-2 * beta * |Real.tanh z|)
        ∂(ProbabilityTheory.gaussianReal 0 (1 : NNReal))) =
      ∫ z : ℝ,
        ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z *
          Real.exp (-2 * beta * |Real.tanh z|) := by
    simpa only [smul_eq_mul] using
      (ProbabilityTheory.integral_gaussianReal_eq_integral_smul
        (E := ℝ) (μ := 0) (v := (1 : NNReal))
        (f := fun z : ℝ => Real.exp (-2 * beta * |Real.tanh z|)) hone)
  rw [hchange]
  have hlap := integrable_standard_gaussian_mul_laplace beta hbeta
  have hconst : Integrable (fun z : ℝ =>
      ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z *
        Real.exp (-2 * beta * Real.tanh 1)) :=
    (ProbabilityTheory.integrable_gaussianPDFReal 0 (1 : NNReal)).mul_const _
  calc
    (∫ z : ℝ,
      ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z *
        Real.exp (-2 * beta * |Real.tanh z|))
        ≤ ∫ z : ℝ,
            ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z *
              Real.exp (-beta * |z|) +
            ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z *
              Real.exp (-2 * beta * Real.tanh 1) := by
          apply integral_mono_of_nonneg
          · exact ae_of_all _ fun z =>
              mul_nonneg
                (ProbabilityTheory.gaussianPDFReal_nonneg 0 (1 : NNReal) z)
                (Real.exp_nonneg _)
          · exact hlap.add hconst
          · exact ae_of_all _ fun z => by
              have henv := gaussian_leakage_sum_envelope beta z hbeta.le
              have hpdf :=
                ProbabilityTheory.gaussianPDFReal_nonneg 0 (1 : NNReal) z
              calc
                ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z *
                    Real.exp (-2 * beta * |Real.tanh z|)
                    ≤ ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z *
                        (Real.exp (-beta * |z|) +
                          Real.exp (-2 * beta * Real.tanh 1)) :=
                      mul_le_mul_of_nonneg_left henv hpdf
                _ = ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z *
                      Real.exp (-beta * |z|) +
                    ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z *
                      Real.exp (-2 * beta * Real.tanh 1) := by ring
    _ = (∫ z : ℝ,
          ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z *
            Real.exp (-beta * |z|)) +
        (∫ z : ℝ,
          ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z *
            Real.exp (-2 * beta * Real.tanh 1)) := by
          rw [integral_add hlap hconst]
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (2 / beta) +
        (∫ z : ℝ,
          ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z *
            Real.exp (-2 * beta * Real.tanh 1)) := by
          exact add_le_add
            (standard_gaussian_laplace_integral_le_peak beta hbeta) (le_refl _)
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * (2 / beta) +
        Real.exp (-2 * beta * Real.tanh 1) := by
          rw [integral_mul_const,
            ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 hone, one_mul]

end RACEFormal