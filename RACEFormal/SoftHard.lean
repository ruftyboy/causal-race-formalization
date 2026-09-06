import Mathlib

namespace RACEFormal

/-- Logistic non-dominant mass used by the one-bit soft RACE distribution. -/
noncomputable def softLeak (beta z : ℝ) : ℝ :=
  1 / (1 + Real.exp (2 * beta * |Real.tanh z|))

/-- A basic logistic tail inequality, independent of the sign of `x`. -/
theorem logistic_tail_le_exp_neg (x : ℝ) :
    1 / (1 + Real.exp x) ≤ Real.exp (-x) := by
  have hden : 0 < 1 + Real.exp x := by positivity
  rw [div_le_iff₀ hden]
  have hprod : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]
    simp
  rw [mul_add, mul_one, hprod]
  linarith [Real.exp_pos (-x)]

/-- The RACE one-bit leakage is bounded by the exponential envelope used in the note. -/
theorem softLeak_le_exp_envelope (beta z : ℝ) :
    softLeak beta z ≤ Real.exp (-2 * beta * |Real.tanh z|) := by
  simpa [softLeak] using
    logistic_tail_le_exp_neg (2 * beta * |Real.tanh z|)

/-- The leakage probability is nonnegative. -/
theorem softLeak_nonneg (beta z : ℝ) : 0 ≤ softLeak beta z := by
  unfold softLeak
  positivity

/-- The leakage probability is at most one. -/
theorem softLeak_le_one (beta z : ℝ) : softLeak beta z ≤ 1 := by
  unfold softLeak
  have hden : 0 < 1 + Real.exp (2 * beta * |Real.tanh z|) := by positivity
  rw [div_le_one hden]
  linarith [Real.exp_pos (2 * beta * |Real.tanh z|)]

/--
If two soft binary distributions have the same dominant hard sign and leakage
masses `r,s`, their agreement differs from the hard collision value `1` by at
most `r+s`.
-/
theorem same_sign_soft_agreement_error
    (r s : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |((1 - r) * (1 - s) + r * s) - 1| ≤ r + s := by
  have hnonneg : 0 ≤ r + s - 2 * r * s := by
    have h₁ : 0 ≤ r * (1 - s) := mul_nonneg hr0 (sub_nonneg.mpr hs1)
    have h₂ : 0 ≤ s * (1 - r) := mul_nonneg hs0 (sub_nonneg.mpr hr1)
    nlinarith
  have hupper : r + s - 2 * r * s ≤ r + s := by
    nlinarith [mul_nonneg hr0 hs0]
  rw [show ((1 - r) * (1 - s) + r * s) - 1 = -(r + s - 2 * r * s) by ring]
  simp only [abs_neg, abs_of_nonneg hnonneg]
  exact hupper

/--
If the two dominant hard signs differ, the soft agreement (whose hard target is
`0`) is again at most the sum of the two leakage masses.
-/
theorem opposite_sign_soft_agreement_error
    (r s : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |(1 - r) * s + r * (1 - s)| ≤ r + s := by
  have hnonneg : 0 ≤ r + s - 2 * r * s := by
    have h₁ : 0 ≤ r * (1 - s) := mul_nonneg hr0 (sub_nonneg.mpr hs1)
    have h₂ : 0 ≤ s * (1 - r) := mul_nonneg hs0 (sub_nonneg.mpr hr1)
    nlinarith
  have hupper : r + s - 2 * r * s ≤ r + s := by
    nlinarith [mul_nonneg hr0 hs0]
  rw [show (1 - r) * s + r * (1 - s) = r + s - 2 * r * s by ring]
  rw [abs_of_nonneg hnonneg]
  exact hupper

end RACEFormal
