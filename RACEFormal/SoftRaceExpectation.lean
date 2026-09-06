import RACEFormal.SoftRaceBit
import RACEFormal.FiniteTemperatureBias

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace RACEFormal

/-- The hard sign bit is a measurable function of its real margin. -/
theorem measurable_hardBit : Measurable hardBit := by
  rw [show hardBit = fun z : ℝ => if z ∈ Set.Ici (0 : ℝ) then true else false by
    funext z
    simp [hardBit, Set.mem_Ici]]
  exact Measurable.ite measurableSet_Ici measurable_const measurable_const

/-- Each coordinate of the one-bit soft RACE distribution is measurable in the margin. -/
theorem measurable_softBitProb (beta : ℝ) (b : Bool) :
    Measurable (fun z : ℝ => softBitProb beta z b) := by
  unfold softBitProb
  apply Measurable.ite
  · exact measurableSet_eq_fun measurable_const measurable_hardBit
  · exact measurable_const.sub (measurable_softLeak beta)
  · exact measurable_softLeak beta

/-- The one-bit soft agreement is measurable in the two margins. -/
theorem measurable_softBitAgreement_pair (beta : ℝ) :
    Measurable (fun p : ℝ × ℝ => softBitAgreement beta p.1 p.2) := by
  unfold softBitAgreement
  apply Finset.measurable_sum
  intro b _hb
  exact ((measurable_softBitProb beta b).comp measurable_fst).mul
    ((measurable_softBitProb beta b).comp measurable_snd)

/-- The hard one-bit collision indicator is measurable in the two margins. -/
theorem measurable_hardBitAgreement_pair :
    Measurable (fun p : ℝ × ℝ => hardBitAgreement p.1 p.2) := by
  unfold hardBitAgreement
  apply Measurable.ite
  · exact measurableSet_eq_fun
      (measurable_hardBit.comp measurable_fst)
      (measurable_hardBit.comp measurable_snd)
  · exact measurable_const
  · exact measurable_const

/-- A one-bit soft agreement composed with two a.e.-measurable margins is integrable. -/
theorem integrable_softBitAgreement_of_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X Y : Ω → ℝ} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (beta : ℝ) :
    Integrable (fun ω => softBitAgreement beta (X ω) (Y ω)) P := by
  refine Integrable.of_bound ?_ (C := 1) ?_
  · exact ((measurable_softBitAgreement_pair beta).comp_aemeasurable
      (hX.prodMk hY)).aestronglyMeasurable
  · exact ae_of_all P fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (softBitAgreement_nonneg beta (X ω) (Y ω))]
      exact softBitAgreement_le_one beta (X ω) (Y ω)

/-- A hard one-bit collision indicator composed with two a.e.-measurable margins is integrable. -/
theorem integrable_hardBitAgreement_of_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X Y : Ω → ℝ} (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    Integrable (fun ω => hardBitAgreement (X ω) (Y ω)) P := by
  refine Integrable.of_bound ?_ (C := 1) ?_
  · exact (measurable_hardBitAgreement_pair.comp_aemeasurable
      (hX.prodMk hY)).aestronglyMeasurable
  · exact ae_of_all P fun ω => by
      have h := hardBitAgreement_mem_Icc (X ω) (Y ω)
      rw [Real.norm_eq_abs, abs_of_nonneg h.1]
      exact h.2

/-- Logistic leakage composed with an a.e.-measurable margin is integrable on a finite measure. -/
theorem integrable_softLeak_of_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) (beta : ℝ) :
    Integrable (fun ω => softLeak beta (X ω)) P := by
  refine Integrable.of_bound ?_ (C := 1) ?_
  · exact ((measurable_softLeak beta).comp_aemeasurable hX).aestronglyMeasurable
  · exact ae_of_all P fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (softLeak_nonneg beta (X ω))]
      exact softLeak_le_one beta (X ω)

/--
The expected one-bit soft RACE agreement differs from the expected hard sign
collision indicator by at most the explicit two-standard-Gaussian leakage
budget.  The two margins may be correlated; only their marginal laws matter.
-/
theorem softBitAgreement_expectation_bias_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0 (1 : NNReal)) P)
    (hY : HasLaw Y (gaussianReal 0 (1 : NNReal)) P)
    (beta : ℝ) (hbeta : 0 < beta) :
    |(∫ ω, softBitAgreement beta (X ω) (Y ω) ∂P) -
      (∫ ω, hardBitAgreement (X ω) (Y ω) ∂P)| ≤
      twoMarginLeakageBudget beta := by
  letI : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hsoft := integrable_softBitAgreement_of_aemeasurable
    hX.aemeasurable hY.aemeasurable beta
  have hhard := integrable_hardBitAgreement_of_aemeasurable
    hX.aemeasurable hY.aemeasurable
  have hleakX := integrable_softLeak_of_aemeasurable hX.aemeasurable beta
  have hleakY := integrable_softLeak_of_aemeasurable hY.aemeasurable beta
  calc
    |(∫ ω, softBitAgreement beta (X ω) (Y ω) ∂P) -
        (∫ ω, hardBitAgreement (X ω) (Y ω) ∂P)|
        = |∫ ω, softBitAgreement beta (X ω) (Y ω) -
            hardBitAgreement (X ω) (Y ω) ∂P| := by
              rw [integral_sub hsoft hhard]
    _ ≤ ∫ ω, |softBitAgreement beta (X ω) (Y ω) -
            hardBitAgreement (X ω) (Y ω)| ∂P :=
          abs_integral_le_integral_abs
    _ ≤ ∫ ω, softLeak beta (X ω) + softLeak beta (Y ω) ∂P := by
          apply integral_mono
          · exact (hsoft.sub hhard).abs
          · exact hleakX.add hleakY
          · exact fun ω =>
              softBitAgreement_error_le_leakage beta (X ω) (Y ω)
    _ = (∫ ω, softLeak beta (X ω) ∂P) +
          (∫ ω, softLeak beta (Y ω) ∂P) := by
            rw [integral_add hleakX hleakY]
    _ ≤ twoMarginLeakageBudget beta :=
      two_standard_gaussian_margins_softLeak_bound hX hY beta hbeta

end RACEFormal
