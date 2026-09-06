import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

open Set Metric MeasureTheory

namespace RACEFormal

noncomputable section

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

local instance : MeasurableSpace Real.Angle := by
  unfold Real.Angle
  infer_instance

local instance : MeasureSpace Real.Angle := by
  unfold Real.Angle
  infer_instance

/-- The norm on `Real.Angle = ℝ / 2πℤ` is the absolute value of its canonical representative. -/
theorem angle_norm_eq_abs_toReal (theta : Real.Angle) :
    ‖theta‖ = |theta.toReal| := by
  calc
    ‖theta‖ = ‖(theta.toReal : Real.Angle)‖ := by
      rw [Real.Angle.coe_toReal]
    _ = |theta.toReal| := by
      apply (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi) (by positivity)).2
      simpa [abs_of_pos Real.pi_pos] using Real.Angle.abs_toReal_le_pi theta

/-- The half-circle on which the cosine is nonnegative. -/
def positiveCosineHemisphere : Set Real.Angle :=
  {theta | 0 ≤ Real.Angle.cos theta}

/-- Membership in the positive-cosine hemisphere is exactly angular distance at most `π/2` from 0. -/
theorem mem_positiveCosineHemisphere_iff_norm_le (theta : Real.Angle) :
    theta ∈ positiveCosineHemisphere ↔ ‖theta‖ ≤ Real.pi / 2 := by
  rw [show theta ∈ positiveCosineHemisphere ↔ 0 ≤ Real.Angle.cos theta by rfl]
  rw [Real.Angle.cos_nonneg_iff_abs_toReal_le_pi_div_two]
  rw [angle_norm_eq_abs_toReal]

/-- The positive-cosine sign region is a closed semicircle centered at angle zero. -/
theorem positiveCosineHemisphere_eq_closedBall :
    positiveCosineHemisphere = Metric.closedBall (0 : Real.Angle) (Real.pi / 2) := by
  ext theta
  rw [mem_positiveCosineHemisphere_iff_norm_le]
  simp only [Metric.mem_closedBall, dist_zero_right]

/-- The positive-cosine semicircle has Haar length `π` inside the angle circle of circumference `2π`. -/
theorem volume_positiveCosineHemisphere :
    (volume : Measure Real.Angle) positiveCosineHemisphere = ENNReal.ofReal Real.pi := by
  rw [positiveCosineHemisphere_eq_closedBall]
  have hball :=
    AddCircle.volume_closedBall (T := 2 * Real.pi)
      (x := (0 : Real.Angle)) (Real.pi / 2)
  have hhalf : 2 * (Real.pi / 2) = Real.pi := by ring
  have hle : Real.pi ≤ 2 * Real.pi := by nlinarith [Real.pi_pos]
  rw [hhalf, min_eq_right hle] at hball
  exact hball

end

end RACEFormal
