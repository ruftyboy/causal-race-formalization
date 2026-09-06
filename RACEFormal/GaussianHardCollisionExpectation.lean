import RACEFormal.GaussianRotatedMargins
import RACEFormal.GaussianHyperplaneProbability
import RACEFormal.SoftRacePowerExpectation

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RACEFormal

/-- The second coordinate of the standard Gaussian plane is nonzero almost surely. -/
theorem ae_standardGaussianPlane_snd_ne_zero :
    ∀ᵐ z ∂standardGaussianPlane, z.2 ≠ 0 := by
  have hzero : standardGaussianPlane {z | z.2 = 0} = 0 := by
    rw [hasLaw_standardGaussianPlane_snd.measure_eq
      (p := fun x : ℝ => x = 0) (measurableSet_singleton 0)]
    letI : NullSingletonClass (gaussianReal 0 (1 : NNReal)) :=
      nullSingletonClass_gaussianReal (by norm_num)
    exact measure_singleton 0
  rw [ae_iff]
  simpa only [Set.compl_ofPred, not_not] using hzero

/-- The rotated standard-Gaussian margin is nonzero almost surely. -/
theorem ae_rotatedGaussianMargin_ne_zero (alpha : ℝ) :
    ∀ᵐ z ∂standardGaussianPlane, rotatedGaussianMargin alpha z ≠ 0 := by
  have hzero : standardGaussianPlane {z | rotatedGaussianMargin alpha z = 0} = 0 := by
    rw [(hasLaw_rotatedGaussianMargin alpha).measure_eq
      (p := fun x : ℝ => x = 0) (measurableSet_singleton 0)]
    letI : NullSingletonClass (gaussianReal 0 (1 : NNReal)) :=
      nullSingletonClass_gaussianReal (by norm_num)
    exact measure_singleton 0
  rw [ae_iff]
  simpa only [Set.compl_ofPred, not_not] using hzero

/--
Away from the two zero-margin tie sets, the hard one-bit agreement is exactly
one minus the indicator of the strict planar Gaussian disagreement wedge.
-/
theorem hardBitAgreement_eq_one_sub_gaussianPlaneDisagreement_indicator
    (alpha : ℝ) (z : ℝ × ℝ)
    (hx : z.2 ≠ 0) (hy : rotatedGaussianMargin alpha z ≠ 0) :
    hardBitAgreement z.2 (rotatedGaussianMargin alpha z) =
      1 - (gaussianPlaneDisagreement alpha).indicator (fun _ => (1 : ℝ)) z := by
  by_cases hxpos : 0 < z.2
  · have hxnonneg : 0 ≤ z.2 := hxpos.le
    have hxbit : hardBit z.2 = true := by simp [hardBit, hxnonneg]
    by_cases hypos : 0 < rotatedGaussianMargin alpha z
    · have hynonneg : 0 ≤ rotatedGaussianMargin alpha z := hypos.le
      have hybit : hardBit (rotatedGaussianMargin alpha z) = true := by
        simp [hardBit, hynonneg]
      have hylinpos :
          0 < z.2 * Real.cos alpha - z.1 * Real.sin alpha := by
        simpa [rotatedGaussianMargin] using hypos
      have hnotmem : z ∉ gaussianPlaneDisagreement alpha := by
        intro hz
        rcases hz with hz | hz
        · exact (not_lt_of_ge hylinpos.le) hz.2
        · exact (not_lt_of_ge hxnonneg) hz.1
      simp [hardBitAgreement, hxbit, hybit, hnotmem]
    · have hyle : rotatedGaussianMargin alpha z ≤ 0 := le_of_not_gt hypos
      have hyneg : rotatedGaussianMargin alpha z < 0 := lt_of_le_of_ne hyle hy
      have hynotnonneg : ¬ 0 ≤ rotatedGaussianMargin alpha z := not_le.mpr hyneg
      have hybit : hardBit (rotatedGaussianMargin alpha z) = false := by
        simp [hardBit, hynotnonneg]
      have hylinneg :
          z.2 * Real.cos alpha - z.1 * Real.sin alpha < 0 := by
        simpa [rotatedGaussianMargin] using hyneg
      have hmem : z ∈ gaussianPlaneDisagreement alpha := by
        exact Or.inl ⟨hxpos, hylinneg⟩
      simp [hardBitAgreement, hxbit, hybit, hmem]
  · have hxle : z.2 ≤ 0 := le_of_not_gt hxpos
    have hxneg : z.2 < 0 := lt_of_le_of_ne hxle hx
    have hxnotnonneg : ¬ 0 ≤ z.2 := not_le.mpr hxneg
    have hxbit : hardBit z.2 = false := by simp [hardBit, hxnotnonneg]
    by_cases hypos : 0 < rotatedGaussianMargin alpha z
    · have hynonneg : 0 ≤ rotatedGaussianMargin alpha z := hypos.le
      have hybit : hardBit (rotatedGaussianMargin alpha z) = true := by
        simp [hardBit, hynonneg]
      have hylinpos :
          0 < z.2 * Real.cos alpha - z.1 * Real.sin alpha := by
        simpa [rotatedGaussianMargin] using hypos
      have hmem : z ∈ gaussianPlaneDisagreement alpha := by
        exact Or.inr ⟨hxneg, hylinpos⟩
      simp [hardBitAgreement, hxbit, hybit, hmem]
    · have hyle : rotatedGaussianMargin alpha z ≤ 0 := le_of_not_gt hypos
      have hyneg : rotatedGaussianMargin alpha z < 0 := lt_of_le_of_ne hyle hy
      have hynotnonneg : ¬ 0 ≤ rotatedGaussianMargin alpha z := not_le.mpr hyneg
      have hybit : hardBit (rotatedGaussianMargin alpha z) = false := by
        simp [hardBit, hynotnonneg]
      have hylinneg :
          z.2 * Real.cos alpha - z.1 * Real.sin alpha < 0 := by
        simpa [rotatedGaussianMargin] using hyneg
      have hnotmem : z ∉ gaussianPlaneDisagreement alpha := by
        intro hz
        rcases hz with hz | hz
        · exact (not_lt_of_ge hxle) hz.1
        · exact (not_lt_of_ge hylinneg.le) hz.2
      simp [hardBitAgreement, hxbit, hybit, hnotmem]

/--
For the same standard Gaussian plane used in the geometric calculation, the
expected hard one-bit collision score is exactly `1 - alpha / π`.
-/
theorem hardBitAgreement_standardGaussianPlane_expectation
    (alpha : ℝ) (ha0 : 0 < alpha) (hapi : alpha < Real.pi) :
    (∫ z, hardBitAgreement z.2 (rotatedGaussianMargin alpha z)
        ∂standardGaussianPlane) = 1 - alpha / Real.pi := by
  letI : IsProbabilityMeasure standardGaussianPlane := by
    unfold standardGaussianPlane
    infer_instance
  have hD : MeasurableSet (gaussianPlaneDisagreement alpha) :=
    measurableSet_gaussianPlaneDisagreement alpha
  have hpoint :
      (fun z => hardBitAgreement z.2 (rotatedGaussianMargin alpha z)) =ᵐ[standardGaussianPlane]
        (fun z => 1 - (gaussianPlaneDisagreement alpha).indicator (fun _ => (1 : ℝ)) z) := by
    filter_upwards [ae_standardGaussianPlane_snd_ne_zero,
      ae_rotatedGaussianMargin_ne_zero alpha] with z hx hy
    exact hardBitAgreement_eq_one_sub_gaussianPlaneDisagreement_indicator alpha z hx hy
  calc
    (∫ z, hardBitAgreement z.2 (rotatedGaussianMargin alpha z)
        ∂standardGaussianPlane)
        = ∫ z, 1 - (gaussianPlaneDisagreement alpha).indicator (fun _ => (1 : ℝ)) z
            ∂standardGaussianPlane := integral_congr_ae hpoint
    _ = (∫ _z, (1 : ℝ) ∂standardGaussianPlane) -
          ∫ z, (gaussianPlaneDisagreement alpha).indicator (fun _ => (1 : ℝ)) z
            ∂standardGaussianPlane := by
          rw [integral_sub (integrable_const (1 : ℝ))
            ((integrable_const (1 : ℝ)).indicator hD)]
    _ = 1 - standardGaussianPlane.real (gaussianPlaneDisagreement alpha) := by
          simp [integral_indicator_const, hD]
    _ = 1 - alpha / Real.pi := by
          unfold standardGaussianPlane
          rw [standardGaussianPlane_disagreement_probability alpha ha0 hapi]

/--
The powered expected soft RACE one-bit kernel is within the explicit
finite-temperature budget of the exact powered angular collision kernel.
-/
theorem powered_softBitAgreement_vs_angular_kernel_bias_le
    (alpha : ℝ) (ha0 : 0 < alpha) (hapi : alpha < Real.pi)
    (Pbits : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    |(∫ z, softBitAgreement beta z.2 (rotatedGaussianMargin alpha z)
        ∂standardGaussianPlane) ^ Pbits -
      (1 - alpha / Real.pi) ^ Pbits| ≤
      (Pbits : ℝ) * twoMarginLeakageBudget beta := by
  have h := powered_softBitAgreement_expectation_bias_le
    hasLaw_standardGaussianPlane_snd (hasLaw_rotatedGaussianMargin alpha)
    Pbits beta hbeta
  rw [hardBitAgreement_standardGaussianPlane_expectation alpha ha0 hapi] at h
  exact h

end RACEFormal
