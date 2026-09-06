import Mathlib

namespace RACEFormal

/--
On the unit interval, raising a kernel score to the `P`th power is `P`-Lipschitz.
This is the deterministic power step used to turn a one-hyperplane soft/hard
agreement error into an entrywise powered-kernel bias bound.
-/
theorem unit_interval_pow_lipschitz
    (P : ℕ) (g p delta : ℝ)
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hdelta : |g - p| ≤ delta) :
    |g ^ P - p ^ P| ≤ (P : ℝ) * delta := by
  have hmax : max |g| |p| ≤ 1 := by
    rw [abs_of_nonneg hg0, abs_of_nonneg hp0]
    exact max_le hg1 hp1
  have hmax0 : 0 ≤ max |g| |p| :=
    (abs_nonneg g).trans (le_max_left |g| |p|)
  have hdelta0 : 0 ≤ delta := (abs_nonneg (g - p)).trans hdelta
  have hP0 : 0 ≤ (P : ℝ) := Nat.cast_nonneg P
  have hpow0 : 0 ≤ max |g| |p| ^ (P - 1) := pow_nonneg hmax0 _
  have hpow1 : max |g| |p| ^ (P - 1) ≤ 1 := pow_le_one₀ hmax0 hmax
  calc
    |g ^ P - p ^ P|
        ≤ |g - p| * (P : ℝ) * max |g| |p| ^ (P - 1) :=
          abs_pow_sub_pow_le g p P
    _ ≤ delta * (P : ℝ) * max |g| |p| ^ (P - 1) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hdelta hP0) hpow0
    _ ≤ delta * (P : ℝ) * 1 := by
      exact mul_le_mul_of_nonneg_left hpow1 (mul_nonneg hdelta0 hP0)
    _ = (P : ℝ) * delta := by ring

/--
If a one-hyperplane soft agreement `g` approximates the hard collision
probability `p` within `delta`, then the `P`-fold factorized soft kernel differs
from the powered angular kernel by at most `P * delta`.
-/
theorem factorized_power_bias
    (P : ℕ) (g p delta : ℝ)
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hgp : |g - p| ≤ delta) :
    |g ^ P - p ^ P| ≤ (P : ℝ) * delta :=
  unit_interval_pow_lipschitz P g p delta hg0 hg1 hp0 hp1 hgp

end RACEFormal
