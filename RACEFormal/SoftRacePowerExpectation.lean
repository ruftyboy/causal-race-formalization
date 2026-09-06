import RACEFormal.SoftRaceExpectation
import RACEFormal.PowerBias

open MeasureTheory ProbabilityTheory

namespace RACEFormal

/--
The expected one-bit soft RACE agreement lies in the unit interval whenever
its two margins have standard Gaussian laws.
-/
theorem softBitAgreement_expectation_mem_Icc
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0 (1 : NNReal)) P)
    (hY : HasLaw Y (gaussianReal 0 (1 : NNReal)) P)
    (beta : ℝ) :
    (∫ ω, softBitAgreement beta (X ω) (Y ω) ∂P) ∈ Set.Icc (0 : ℝ) 1 := by
  letI : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hsoft := integrable_softBitAgreement_of_aemeasurable
    hX.aemeasurable hY.aemeasurable beta
  constructor
  · exact integral_nonneg fun ω =>
      softBitAgreement_nonneg beta (X ω) (Y ω)
  · calc
      (∫ ω, softBitAgreement beta (X ω) (Y ω) ∂P)
          ≤ ∫ _ω, (1 : ℝ) ∂P := by
            apply integral_mono hsoft (integrable_const (1 : ℝ))
            intro ω
            exact softBitAgreement_le_one beta (X ω) (Y ω)
      _ = 1 := by simp

/--
The expected hard one-bit collision indicator lies in the unit interval.
-/
theorem hardBitAgreement_expectation_mem_Icc
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0 (1 : NNReal)) P)
    (hY : HasLaw Y (gaussianReal 0 (1 : NNReal)) P) :
    (∫ ω, hardBitAgreement (X ω) (Y ω) ∂P) ∈ Set.Icc (0 : ℝ) 1 := by
  letI : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hhard := integrable_hardBitAgreement_of_aemeasurable
    hX.aemeasurable hY.aemeasurable
  constructor
  · exact integral_nonneg fun ω =>
      (hardBitAgreement_mem_Icc (X ω) (Y ω)).1
  · calc
      (∫ ω, hardBitAgreement (X ω) (Y ω) ∂P)
          ≤ ∫ _ω, (1 : ℝ) ∂P := by
            apply integral_mono hhard (integrable_const (1 : ℝ))
            intro ω
            exact (hardBitAgreement_mem_Icc (X ω) (Y ω)).2
      _ = 1 := by simp

/--
For `Pbits` factorized hyperplanes, powering the expected one-bit soft and
hard collision scores amplifies the one-bit finite-temperature bias by at
most the usual `Pbits` Lipschitz factor.

This is the scalar factorization bridge needed before identifying the hard
one-bit expectation with the exact angular collision kernel.
-/
theorem powered_softBitAgreement_expectation_bias_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0 (1 : NNReal)) P)
    (hY : HasLaw Y (gaussianReal 0 (1 : NNReal)) P)
    (Pbits : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    |(∫ ω, softBitAgreement beta (X ω) (Y ω) ∂P) ^ Pbits -
      (∫ ω, hardBitAgreement (X ω) (Y ω) ∂P) ^ Pbits| ≤
      (Pbits : ℝ) * twoMarginLeakageBudget beta := by
  have hg := softBitAgreement_expectation_mem_Icc hX hY beta
  have hp := hardBitAgreement_expectation_mem_Icc hX hY
  exact factorized_power_bias Pbits
    (∫ ω, softBitAgreement beta (X ω) (Y ω) ∂P)
    (∫ ω, hardBitAgreement (X ω) (Y ω) ∂P)
    (twoMarginLeakageBudget beta)
    hg.1 hg.2 hp.1 hp.2
    (softBitAgreement_expectation_bias_le hX hY beta hbeta)

end RACEFormal
