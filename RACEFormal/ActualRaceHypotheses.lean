import RACEFormal.ActualRaceSampler
import RACEFormal.GaussianHyperplaneSampler
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.Integration

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace RACEFormal

/-- The logistic leakage used by RACE is strictly positive. -/
theorem softLeak_pos (beta z : ℝ) : 0 < softLeak beta z := by
  unfold softLeak
  positivity

/-- The logistic leakage used by RACE is strictly smaller than one. -/
theorem softLeak_lt_one (beta z : ℝ) : softLeak beta z < 1 := by
  unfold softLeak
  have hden : 0 < 1 + Real.exp (2 * beta * |Real.tanh z|) := by positivity
  rw [div_lt_one hden]
  linarith [Real.exp_pos (2 * beta * |Real.tanh z|)]

/-- Both entries of the binary soft-hash distribution are strictly positive. -/
theorem softBitProb_pos (beta z : ℝ) (b : Bool) :
    0 < softBitProb beta z b := by
  unfold softBitProb
  by_cases h : b = hardBit z
  · rw [if_pos h]
    exact sub_pos.mpr (softLeak_lt_one beta z)
  · rw [if_neg h]
    exact softLeak_pos beta z

/-- The one-hyperplane soft collision score is strictly positive. -/
theorem softBitAgreement_pos (beta x y : ℝ) :
    0 < softBitAgreement beta x y := by
  unfold softBitAgreement
  rw [Fintype.sum_bool]
  exact add_pos
    (mul_pos (softBitProb_pos beta x true) (softBitProb_pos beta y true))
    (mul_pos (softBitProb_pos beta x false) (softBitProb_pos beta y false))

/-- Projection onto a fixed vector is measurable as a function of the Gaussian plane. -/
theorem measurable_raceProjection_fixed {d : ℕ} (x : RaceAmbient d) :
    Measurable (fun w : RaceHyperplane d => raceProjection w x) := by
  unfold raceProjection
  fun_prop

/-- A one-plane soft agreement score is measurable. -/
theorem measurable_softBitAgreement_projection {d : ℕ}
    (q k : RaceAmbient d) (beta : ℝ) :
    Measurable (fun w : RaceHyperplane d =>
      softBitAgreement beta (raceProjection w q) (raceProjection w k)) := by
  have hpair : Measurable (fun w : RaceHyperplane d =>
      (raceProjection w q, raceProjection w k)) :=
    Measurable.prod
      (measurable_raceProjection_fixed q)
      (measurable_raceProjection_fixed k)
  simpa [Function.comp_def] using
    (measurable_softBitAgreement_pair beta).comp hpair

/-- One sampled RACE bit score is a measurable function of the full hyperplane draw. -/
theorem measurable_sampledRaceBitScore
    {N L Pbits d : ℕ}
    (Q K : Fin N → RaceAmbient d) (beta : ℝ)
    (pair : CausalPair N) (table : Fin L) (bit : Fin Pbits) :
    Measurable (sampledRaceBitScore Q K beta pair table bit) := by
  change Measurable (fun ω : RaceHyperplaneArray L Pbits d =>
    softBitAgreement beta
      (raceProjection (ω (table, bit)) (Q pair.1))
      (raceProjection (ω (table, bit)) (K (causalPairKeyIndex pair))))
  exact (measurable_softBitAgreement_projection
    (Q pair.1) (K (causalPairKeyIndex pair)) beta).comp
      (measurable_pi_apply (table, bit))

/-- For a fixed causal pair and table, the actual sampled bit scores are independent. -/
theorem sampledRaceBitScores_iIndep
    {N L Pbits d : ℕ}
    (Q K : Fin N → RaceAmbient d) (beta : ℝ)
    (pair : CausalPair N) (table : Fin L) :
    iIndepFun (fun bit => sampledRaceBitScore Q K beta pair table bit)
      (standardRaceHyperplaneArrayLaw L Pbits d) := by
  let g : Fin Pbits → RaceHyperplane d → ℝ := fun _ w =>
    softBitAgreement beta
      (raceProjection w (Q pair.1))
      (raceProjection w (K (causalPairKeyIndex pair)))
  have hg : ∀ bit, Measurable (g bit) := by
    intro bit
    exact measurable_softBitAgreement_projection
      (Q pair.1) (K (causalPairKeyIndex pair)) beta
  have hcomp := (raceTableHyperplanes_iIndep L Pbits d table).comp g hg
  have heq : ∀ bit : Fin Pbits,
      sampledRaceBitScore Q K beta pair table bit =ᵐ[
        standardRaceHyperplaneArrayLaw L Pbits d]
        (g bit ∘ fun ω : RaceHyperplaneArray L Pbits d => ω (table, bit)) := by
    intro bit
    exact Filter.Eventually.of_forall (fun ω => by rfl)
  exact (iIndepFun_congr heq).2 hcomp

/-- The planes belonging to one table, collected as a vector. -/
def raceTablePlaneVector
    {L Pbits d : ℕ} (table : Fin L)
    (ω : RaceHyperplaneArray L Pbits d) : Fin Pbits → RaceHyperplane d :=
  fun bit => ω (table, bit)

/-- One table-vector has the product law of `Pbits` independent Gaussian planes. -/
theorem raceTablePlaneVector_hasLaw
    (L Pbits d : ℕ) (table : Fin L) :
    HasLaw (raceTablePlaneVector (Pbits := Pbits) (d := d) table)
      (Measure.pi (fun _ : Fin Pbits => standardRaceHyperplaneLaw d))
      (standardRaceHyperplaneArrayLaw L Pbits d) := by
  change HasLaw (fun (ω : RaceHyperplaneArray L Pbits d) bit => ω (table, bit))
    (Measure.pi (fun _ : Fin Pbits => standardRaceHyperplaneLaw d))
    (standardRaceHyperplaneArrayLaw L Pbits d)
  exact (raceTableHyperplanes_iIndep L Pbits d table).hasLaw_pi
    (fun bit => raceHyperplane_hasLaw L Pbits d (table, bit))

/--
The `L` table-vectors themselves are independent.  This formally groups the
flat `torch.randn(L, Pbits, d)` product sampler into independent table blocks.
-/
theorem raceTablePlaneVectors_iIndep
    (L Pbits d : ℕ) :
    iIndepFun
      (fun table => raceTablePlaneVector (Pbits := Pbits) (d := d) table)
      (standardRaceHyperplaneArrayLaw L Pbits d) := by
  let ν : Measure (RaceHyperplane d) := standardRaceHyperplaneLaw d
  let τ : Fin L → Measure (Fin Pbits → RaceHyperplane d) := fun _ =>
    Measure.pi (fun _ : Fin Pbits => ν)
  have htable : ∀ table : Fin L,
      HasLaw (raceTablePlaneVector (Pbits := Pbits) (d := d) table)
        (τ table) (standardRaceHyperplaneArrayLaw L Pbits d) := by
    intro table
    simpa [τ, ν] using raceTablePlaneVector_hasLaw L Pbits d table
  apply (iIndepFun_iff_hasLaw_pi_pi htable).2
  refine ⟨?_, ?_⟩
  · rw [aemeasurable_pi_iff]
    intro table
    rw [aemeasurable_pi_iff]
    intro bit
    exact (measurable_pi_apply (table, bit)).aemeasurable
  · have hfun :
        (fun (ω : RaceHyperplaneArray L Pbits d) table =>
          raceTablePlaneVector (Pbits := Pbits) (d := d) table ω) =
        (MeasurableEquiv.curry (Fin L) (Fin Pbits) (RaceHyperplane d)) := by
        funext ω table bit
        rfl
    rw [hfun]
    unfold standardRaceHyperplaneArrayLaw
    have hcurry := Measure.infinitePi_map_curry
      (μ := fun (_ : Fin L) (_ : Fin Pbits) => standardRaceHyperplaneLaw d)
    simpa [τ, ν, Measure.infinitePi_eq_pi] using hcurry

/-- One actual sampled RACE table score is measurable. -/
theorem measurable_sampledRaceTableScore
    {N L Pbits d : ℕ}
    (Q K : Fin N → RaceAmbient d) (beta : ℝ)
    (pair : CausalPair N) (table : Fin L) :
    Measurable (sampledRaceTableScore (Pbits := Pbits) Q K beta pair table) := by
  unfold sampledRaceTableScore
  exact Finset.measurable_prod Finset.univ (fun bit _ =>
    measurable_sampledRaceBitScore Q K beta pair table bit)

/-- For each causal pair, the actual scores of the `L` independent tables are independent. -/
theorem sampledRaceTableScores_iIndep
    {N L Pbits d : ℕ}
    (Q K : Fin N → RaceAmbient d) (beta : ℝ)
    (pair : CausalPair N) :
    iIndepFun (fun table =>
      sampledRaceTableScore (Pbits := Pbits) Q K beta pair table)
      (standardRaceHyperplaneArrayLaw L Pbits d) := by
  let g : Fin L → (Fin Pbits → RaceHyperplane d) → ℝ := fun _ planes =>
    ∏ bit, softBitAgreement beta
      (raceProjection (planes bit) (Q pair.1))
      (raceProjection (planes bit) (K (causalPairKeyIndex pair)))
  have hg : ∀ table, Measurable (g table) := by
    intro table
    dsimp [g]
    apply Finset.measurable_prod
    intro bit _
    exact (measurable_softBitAgreement_projection
      (Q pair.1) (K (causalPairKeyIndex pair)) beta).comp
        (measurable_pi_apply bit)
  have hcomp := (raceTablePlaneVectors_iIndep L Pbits d).comp g hg
  have heq : ∀ table : Fin L,
      sampledRaceTableScore (Pbits := Pbits) Q K beta pair table =ᵐ[
        standardRaceHyperplaneArrayLaw L Pbits d]
        (g table ∘ raceTablePlaneVector (Pbits := Pbits) (d := d) table) := by
    intro table
    exact Filter.Eventually.of_forall (fun ω => by rfl)
  exact (iIndepFun_congr heq).2 hcomp

/-- Every actual one-bit sampled score lies in `[0,1]`. -/
theorem sampledRaceBitScore_mem_Icc
    {N L Pbits d : ℕ}
    (Q K : Fin N → RaceAmbient d) (beta : ℝ)
    (pair : CausalPair N) (table : Fin L) (bit : Fin Pbits)
    (ω : RaceHyperplaneArray L Pbits d) :
    sampledRaceBitScore Q K beta pair table bit ω ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨softBitAgreement_nonneg _ _ _, softBitAgreement_le_one _ _ _⟩

/-- Every actual one-bit sampled score is strictly positive. -/
theorem sampledRaceBitScore_pos
    {N L Pbits d : ℕ}
    (Q K : Fin N → RaceAmbient d) (beta : ℝ)
    (pair : CausalPair N) (table : Fin L) (bit : Fin Pbits)
    (ω : RaceHyperplaneArray L Pbits d) :
    0 < sampledRaceBitScore Q K beta pair table bit ω := by
  exact softBitAgreement_pos _ _ _

/-- Every actual sampled table score lies in `[0,1]`. -/
theorem sampledRaceTableScore_mem_Icc
    {N L Pbits d : ℕ}
    (Q K : Fin N → RaceAmbient d) (beta : ℝ)
    (pair : CausalPair N) (table : Fin L)
    (ω : RaceHyperplaneArray L Pbits d) :
    sampledRaceTableScore (Pbits := Pbits) Q K beta pair table ω ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · unfold sampledRaceTableScore
    exact Finset.prod_nonneg (fun bit _ =>
      (sampledRaceBitScore_mem_Icc Q K beta pair table bit ω).1)
  · unfold sampledRaceTableScore
    let f : Fin Pbits → ℝ := fun bit =>
      sampledRaceBitScore Q K beta pair table bit ω
    have h0 : ∀ bit, 0 ≤ f bit := fun bit =>
      (sampledRaceBitScore_mem_Icc Q K beta pair table bit ω).1
    have h1 : ∀ bit, f bit ≤ 1 := fun bit =>
      (sampledRaceBitScore_mem_Icc Q K beta pair table bit ω).2
    have hprod : ∀ s : Finset (Fin Pbits), (∏ bit ∈ s, f bit) ≤ 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
          rw [Finset.prod_insert ha]
          have hs0 : 0 ≤ ∏ bit ∈ s, f bit :=
            Finset.prod_nonneg (fun bit _ => h0 bit)
          exact (mul_le_of_le_one_left hs0 (h1 a)).trans ih
    simpa [f] using hprod Finset.univ

/-- Every actual sampled table score is strictly positive. -/
theorem sampledRaceTableScore_pos
    {N L Pbits d : ℕ}
    (Q K : Fin N → RaceAmbient d) (beta : ℝ)
    (pair : CausalPair N) (table : Fin L)
    (ω : RaceHyperplaneArray L Pbits d) :
    0 < sampledRaceTableScore (Pbits := Pbits) Q K beta pair table ω := by
  unfold sampledRaceTableScore
  exact Finset.prod_pos (fun bit _ =>
    sampledRaceBitScore_pos Q K beta pair table bit ω)

/--
For an angular query/key pair, the mean of an actual sampled bit score is the
canonical planar soft-RACE mean used by the bias theorem.
-/
theorem sampledRaceBitScore_integral_eq_planar
    {N L Pbits d : ℕ}
    (Q K : Fin N → RaceAmbient d) (alpha : CausalPair N → ℝ)
    (beta : ℝ) (pair : CausalPair N) (table : Fin L) (bit : Fin Pbits)
    (hgeom : IsAngularPairGeometry (ι := Fin d)
      (Q pair.1) (K (causalPairKeyIndex pair)) (alpha pair)) :
    (∫ ω, sampledRaceBitScore Q K beta pair table bit ω
        ∂standardRaceHyperplaneArrayLaw L Pbits d) =
      ∫ z, softBitAgreement beta z.2
        (rotatedGaussianMargin (alpha pair) z) ∂standardGaussianPlane := by
  let f : RaceHyperplane d → ℝ := fun w =>
    softBitAgreement beta
      (raceProjection w (Q pair.1))
      (raceProjection w (K (causalPairKeyIndex pair)))
  have hf : AEStronglyMeasurable f (standardRaceHyperplaneLaw d) :=
    (measurable_softBitAgreement_projection
      (Q pair.1) (K (causalPairKeyIndex pair)) beta).aestronglyMeasurable
  have hlaw := raceHyperplane_hasLaw L Pbits d (table, bit)
  calc
    (∫ ω, sampledRaceBitScore Q K beta pair table bit ω
        ∂standardRaceHyperplaneArrayLaw L Pbits d)
        = ∫ w, f w ∂standardRaceHyperplaneLaw d := by
          simpa [f, sampledRaceBitScore] using hlaw.integral_comp hf
    _ = ∫ z, softBitAgreement beta z.2
          (rotatedGaussianMargin (alpha pair) z) ∂standardGaussianPlane := by
          unfold standardRaceHyperplaneLaw
          simpa [f, raceProjection, real_inner_comm] using
            gaussian_hyperplane_softBitAgreement_expectation
              (Q pair.1) (K (causalPairKeyIndex pair)) (alpha pair) beta hgeom

end RACEFormal
