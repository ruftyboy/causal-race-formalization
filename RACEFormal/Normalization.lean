import Mathlib

open scoped BigOperators

namespace RACEFormal

/--
Deterministic normalization estimate used in the causal RACE note.

For nonnegative score vectors `a,b`, with positive masses
`A = ∑ a`, `B = ∑ b`, let `η = ∑ |a-b|`. Then the L1 distance
between the normalized vectors is at most `2η/A`.
-/
theorem normalization_l1_bound
    {m : ℕ} (a b : Fin m → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hA : 0 < ∑ j, a j) (hB : 0 < ∑ j, b j) :
    (∑ j, |a j / (∑ i, a i) - b j / (∑ i, b i)|)
      ≤ 2 * (∑ j, |a j - b j|) / (∑ i, a i) := by
  let A : ℝ := ∑ j, a j
  let B : ℝ := ∑ j, b j
  let η : ℝ := ∑ j, |a j - b j|
  have hApos : 0 < A := by simpa [A] using hA
  have hBpos : 0 < B := by simpa [B] using hB
  have hA0 : A ≠ 0 := ne_of_gt hApos
  have hB0 : B ≠ 0 := ne_of_gt hBpos

  have hmass : |A - B| ≤ η := by
    calc
      |A - B| = |∑ j, (a j - b j)| := by
        simp [A, B, Finset.sum_sub_distrib]
      _ ≤ ∑ j, |a j - b j| := Finset.abs_sum_le_sum_abs _ _
      _ = η := rfl

  have hfirst : (∑ j, |a j / A - b j / A|) = η / A := by
    calc
      (∑ j, |a j / A - b j / A|)
          = ∑ j, (|a j - b j| / A) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [← sub_div, abs_div, abs_of_pos hApos]
      _ = (∑ j, |a j - b j|) / A := by
            rw [Finset.sum_div]
      _ = η / A := rfl

  have hrecip : B * |1 / A - 1 / B| = |A - B| / A := by
    have hABpos : 0 < A * B := mul_pos hApos hBpos
    have hfrac : (1 / A - 1 / B) = (B - A) / (A * B) := by
      field_simp [hA0, hB0]
    rw [hfrac, abs_div, abs_of_pos hABpos, abs_sub_comm]
    field_simp [hA0, hB0]

  have hsecond : (∑ j, |b j / A - b j / B|) = |A - B| / A := by
    calc
      (∑ j, |b j / A - b j / B|)
          = ∑ j, (b j * |1 / A - 1 / B|) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hbj : |b j| = b j := abs_of_nonneg (hb j)
              calc
                |b j / A - b j / B|
                    = |b j * (1 / A - 1 / B)| := by
                        congr 1
                        field_simp [hA0, hB0]
                _ = b j * |1 / A - 1 / B| := by
                      rw [abs_mul, hbj]
      _ = B * |1 / A - 1 / B| := by
            simp [B, Finset.sum_mul]
      _ = |A - B| / A := hrecip

  have hpoint (j : Fin m) :
      |a j / A - b j / B|
        ≤ |a j / A - b j / A| + |b j / A - b j / B| := by
    calc
      |a j / A - b j / B|
          = |(a j / A - b j / A) + (b j / A - b j / B)| := by ring_nf
      _ ≤ |a j / A - b j / A| + |b j / A - b j / B| := abs_add_le _ _

  have hmain : (∑ j, |a j / A - b j / B|) ≤ 2 * η / A := by
    calc
      (∑ j, |a j / A - b j / B|)
          ≤ ∑ j, (|a j / A - b j / A| + |b j / A - b j / B|) := by
              exact Finset.sum_le_sum fun j hj => hpoint j
      _ = (∑ j, |a j / A - b j / A|) + (∑ j, |b j / A - b j / B|) := by
            rw [Finset.sum_add_distrib]
      _ = η / A + |A - B| / A := by rw [hfirst, hsecond]
      _ ≤ η / A + η / A := by
            gcongr
      _ = 2 * η / A := by ring

  simpa [A, B, η] using hmain

end RACEFormal
