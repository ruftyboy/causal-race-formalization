import RACEFormal.GaussianLeakage
import RACEFormal.SoftHard
import RACEFormal.PowerBias
import Mathlib.Probability.HasLaw

open MeasureTheory ProbabilityTheory

namespace RACEFormal

/-- The one-margin Gaussian leakage budget appearing in the finite-temperature RACE bound. -/
noncomputable def oneMarginLeakageBudget (beta : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * (2 / beta) +
    Real.exp (-2 * beta * Real.tanh 1)

/-- The corresponding two-margin soft/hard budget. -/
noncomputable def twoMarginLeakageBudget (beta : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * (4 / beta) +
    2 * Real.exp (-2 * beta * Real.tanh 1)

/-- Measurability of the real hyperbolic tangent, exposed explicitly for the probability layer. -/
theorem measurable_real_tanh : Measurable Real.tanh := by
  rw [show Real.tanh = (fun x : ℝ => Real.sinh x / Real.cosh x) by
    funext x
    exact Real.tanh_eq_sinh_div_cosh x]
  exact Real.measurable_sinh.div Real.measurable_cosh

/-- Measurability of the exponential leakage envelope. -/
theorem measurable_gaussian_leakage_envelope (beta : ℝ) :
    Measurable (fun z : ℝ => Real.exp (-2 * beta * |Real.tanh z|)) := by
  exact (measurable_const.mul measurable_real_tanh.abs).exp

/-- Measurability of the actual logistic one-bit leakage. -/
theorem measurable_softLeak (beta : ℝ) : Measurable (softLeak beta) := by
  unfold softLeak
  exact measurable_const.div
    (measurable_const.add (measurable_const.mul measurable_real_tanh.abs).exp)

/-- The exponential leakage envelope is integrable under the standard Gaussian law. -/
theorem integrable_standard_gaussian_leakage_envelope
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Integrable (fun z : ℝ => Real.exp (-2 * beta * |Real.tanh z|))
      (gaussianReal 0 (1 : NNReal)) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_gaussian_leakage_envelope beta).aestronglyMeasurable ?_
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [Real.exp_le_one_iff]
    have hz : 0 ≤ |Real.tanh z| := abs_nonneg _
    nlinarith

/-- The actual logistic soft leakage inherits the Gaussian envelope expectation bound. -/
theorem standard_gaussian_softLeak_expectation_bound
    (beta : ℝ) (hbeta : 0 < beta) :
    (∫ z : ℝ, softLeak beta z ∂(gaussianReal 0 (1 : NNReal))) ≤
      oneMarginLeakageBudget beta := by
  calc
    (∫ z : ℝ, softLeak beta z ∂(gaussianReal 0 (1 : NNReal)))
        ≤ ∫ z : ℝ, Real.exp (-2 * beta * |Real.tanh z|)
            ∂(gaussianReal 0 (1 : NNReal)) := by
          apply integral_mono_of_nonneg
          · exact ae_of_all _ fun z => softLeak_nonneg beta z
          · exact integrable_standard_gaussian_leakage_envelope beta hbeta.le
          · exact ae_of_all _ fun z => softLeak_le_exp_envelope beta z
    _ ≤ oneMarginLeakageBudget beta := by
      simpa [oneMarginLeakageBudget] using
        standard_gaussian_leakage_expectation_bound beta hbeta

/-- Any random margin with standard Gaussian law obeys the same soft-leak expectation bound. -/
theorem softLeak_expectation_of_hasLaw_standardGaussian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0 (1 : NNReal)) P)
    (beta : ℝ) (hbeta : 0 < beta) :
    (∫ ω, softLeak beta (X ω) ∂P) ≤ oneMarginLeakageBudget beta := by
  have hmeas : AEStronglyMeasurable (softLeak beta)
      (gaussianReal 0 (1 : NNReal)) :=
    (measurable_softLeak beta).aestronglyMeasurable
  calc
    (∫ ω, softLeak beta (X ω) ∂P)
        = ∫ z : ℝ, softLeak beta z ∂(gaussianReal 0 (1 : NNReal)) := by
          simpa only [Function.comp_apply] using hX.integral_comp hmeas
    _ ≤ oneMarginLeakageBudget beta :=
      standard_gaussian_softLeak_expectation_bound beta hbeta

/--
For two possibly correlated margins whose marginals are each standard Gaussian,
the expected sum of the two soft leakage masses is bounded by the explicit
RACE finite-temperature one-bit term.  No independence between the two margins
is required.
-/
theorem two_standard_gaussian_margins_softLeak_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0 (1 : NNReal)) P)
    (hY : HasLaw Y (gaussianReal 0 (1 : NNReal)) P)
    (beta : ℝ) (hbeta : 0 < beta) :
    (∫ ω, softLeak beta (X ω) ∂P) +
      (∫ ω, softLeak beta (Y ω) ∂P) ≤
      twoMarginLeakageBudget beta := by
  have hx := softLeak_expectation_of_hasLaw_standardGaussian hX beta hbeta
  have hy := softLeak_expectation_of_hasLaw_standardGaussian hY beta hbeta
  calc
    (∫ ω, softLeak beta (X ω) ∂P) +
        (∫ ω, softLeak beta (Y ω) ∂P)
        ≤ oneMarginLeakageBudget beta + oneMarginLeakageBudget beta :=
          add_le_add hx hy
    _ = twoMarginLeakageBudget beta := by
      simp [oneMarginLeakageBudget, twoMarginLeakageBudget]
      ring

/--
Multiplying the one-bit soft/hard error budget by the `Pbits` power-Lipschitz
factor yields the full powered-kernel finite-temperature bias budget.
-/
theorem powered_finite_temperature_bias_budget
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0 (1 : NNReal)) P)
    (hY : HasLaw Y (gaussianReal 0 (1 : NNReal)) P)
    (Pbits : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    (Pbits : ℝ) *
        ((∫ ω, softLeak beta (X ω) ∂P) +
          (∫ ω, softLeak beta (Y ω) ∂P)) ≤
      (Pbits : ℝ) * twoMarginLeakageBudget beta := by
  exact mul_le_mul_of_nonneg_left
    (two_standard_gaussian_margins_softLeak_bound hX hY beta hbeta)
    (Nat.cast_nonneg Pbits)

end RACEFormal
