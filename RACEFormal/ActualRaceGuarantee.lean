import RACEFormal.ActualRaceHypotheses
import RACEFormal.FinalCausalRaceGuarantee

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace RACEFormal

/-- The causal `L`-table score average produced by the actual Gaussian RACE sampler. -/
noncomputable def actualCausalRaceAverage
    {N L Pbits d : ℕ}
    (Q K : Fin N → RaceAmbient d) (beta : ℝ)
    (p : CausalPair N) (ω : RaceHyperplaneArray L Pbits d) : ℝ :=
  causalRaceAverage (sampledRaceBitScore Q K beta) p ω

/-- Simultaneous causal-triangle failure event for the actual RACE sampler. -/
def actualCausalRaceBadSet
    {N L Pbits d : ℕ}
    (Q K : Fin N → RaceAmbient d) (alpha : CausalPair N → ℝ)
    (beta eps : ℝ) : Set (RaceHyperplaneArray L Pbits d) :=
  causalRaceBadSet (sampledRaceBitScore Q K beta) alpha eps

/-- The powered angular target is strictly positive whenever the pair angle is below `π`. -/
theorem causalRaceAngularTarget_pos_of_lt_pi
    {N Pbits : ℕ} (alpha : CausalPair N → ℝ)
    (halphapi : ∀ p, alpha p < Real.pi) (p : CausalPair N) :
    0 < causalRaceAngularTarget (Pbits := Pbits) alpha p := by
  unfold causalRaceAngularTarget
  exact pow_pos (sub_pos.mpr ((div_lt_one Real.pi_pos).2 (halphapi p))) _

/-- Every causal prefix has strictly positive exact angular mass. -/
theorem causalRaceAngularTarget_prefix_mass_pos
    {N Pbits : ℕ} (alpha : CausalPair N → ℝ)
    (halphapi : ∀ p, alpha p < Real.pi) (t : Fin N) :
    0 < ∑ j : Fin (t.1 + 1),
      causalRaceAngularTarget (Pbits := Pbits) alpha
        (⟨t, j⟩ : CausalPair N) := by
  let j0 : Fin (t.1 + 1) := ⟨0, Nat.succ_pos t.1⟩
  apply Finset.sum_pos'
  · intro j _
    exact (causalRaceAngularTarget_pos_of_lt_pi alpha halphapi
      (⟨t, j⟩ : CausalPair N)).le
  · exact ⟨j0, Finset.mem_univ j0,
      causalRaceAngularTarget_pos_of_lt_pi alpha halphapi
        (⟨t, j0⟩ : CausalPair N)⟩

/-- Every realized actual RACE pair-score average is strictly positive when `L > 0`. -/
theorem actualCausalRaceAverage_pos
    {N L Pbits d : ℕ} (hL : 0 < L)
    (Q K : Fin N → RaceAmbient d) (beta : ℝ)
    (p : CausalPair N) (ω : RaceHyperplaneArray L Pbits d) :
    0 < actualCausalRaceAverage (L := L) (Pbits := Pbits) Q K beta p ω := by
  unfold actualCausalRaceAverage causalRaceAverage
  have hsum :
      0 < ∑ i : Fin L, ∏ k : Fin Pbits,
        sampledRaceBitScore Q K beta p i k ω := by
    let i0 : Fin L := ⟨0, hL⟩
    apply Finset.sum_pos'
    · intro i _
      simpa [sampledRaceTableScore] using
        (sampledRaceTableScore_pos Q K beta p i ω).le
    · exact ⟨i0, Finset.mem_univ i0, by
        simpa [sampledRaceTableScore] using
          sampledRaceTableScore_pos Q K beta p i0 ω⟩
  have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
  exact mul_pos (inv_pos.mpr hLr) hsum

/-- Every causal prefix has positive realized score mass for the actual sampler. -/
theorem actualCausalRaceAverage_prefix_mass_pos
    {N L Pbits d : ℕ} (hL : 0 < L)
    (Q K : Fin N → RaceAmbient d) (beta : ℝ)
    (ω : RaceHyperplaneArray L Pbits d) (t : Fin N) :
    0 < ∑ j : Fin (t.1 + 1),
      actualCausalRaceAverage (L := L) (Pbits := Pbits) Q K beta
        (⟨t, j⟩ : CausalPair N) ω := by
  let j0 : Fin (t.1 + 1) := ⟨0, Nat.succ_pos t.1⟩
  apply Finset.sum_pos'
  · intro j _
    exact (actualCausalRaceAverage_pos hL Q K beta
      (⟨t, j⟩ : CausalPair N) ω).le
  · exact ⟨j0, Finset.mem_univ j0,
      actualCausalRaceAverage_pos hL Q K beta
        (⟨t, j0⟩ : CausalPair N) ω⟩

/--
High-probability causal RACE guarantee with the abstract sampler hypotheses
fully discharged by the concrete `L × Pbits` independent standard-Gaussian
random-hyperplane construction.
-/
theorem actual_race_high_probability_output_guarantee
    {E : Type*} {N L Pbits d : ℕ}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hL : 0 < L)
    (Q K : Fin N → RaceAmbient d)
    (alpha : CausalPair N → ℝ)
    (beta : ℝ) (hbeta : 0 < beta)
    (halpha0 : ∀ p, 0 < alpha p)
    (halphapi : ∀ p, alpha p < Real.pi)
    (hgeom : ∀ p, IsAngularPairGeometry (ι := Fin d)
      (Q p.1) (K (causalPairKeyIndex p)) (alpha p))
    (V : (t : Fin N) → Fin (t.1 + 1) → E)
    (D : Fin N → ℝ)
    (hD : ∀ t, 0 ≤ D t)
    (hdiam : ∀ t j k, ‖V t j - V t k‖ ≤ D t)
    {u : ℝ} (hu : 0 ≤ u) :
    let B := (Pbits : ℝ) * twoMarginLeakageBudget beta
    let eps := u + B
    (standardRaceHyperplaneArrayLaw L Pbits d).real
        (actualCausalRaceBadSet (L := L) (Pbits := Pbits)
          Q K alpha beta eps)
      ≤ (Fintype.card (CausalPair N) : ℝ) *
        (2 * Real.exp (-((L : ℝ) * u) ^ 2 /
          (2 * (∑ _i : Fin L, ((1 / 2 : ℝ≥0) ^ 2) : ℝ≥0)))) ∧
      ∀ ω, ω ∉ actualCausalRaceBadSet (L := L) (Pbits := Pbits)
          Q K alpha beta eps → ∀ t : Fin N,
        ‖∑ j : Fin (t.1 + 1),
            (actualCausalRaceAverage (L := L) (Pbits := Pbits)
                Q K beta (⟨t, j⟩ : CausalPair N) ω /
                (∑ i : Fin (t.1 + 1),
                  actualCausalRaceAverage (L := L) (Pbits := Pbits)
                    Q K beta (⟨t, i⟩ : CausalPair N) ω) -
              causalRaceAngularTarget (Pbits := Pbits) alpha
                  (⟨t, j⟩ : CausalPair N) /
                (∑ i : Fin (t.1 + 1),
                  causalRaceAngularTarget (Pbits := Pbits) alpha
                    (⟨t, i⟩ : CausalPair N))) • V t j‖
          ≤ D t * min 1
            (eps /
              ((∑ i : Fin (t.1 + 1),
                  causalRaceAngularTarget (Pbits := Pbits) alpha
                    (⟨t, i⟩ : CausalPair N)) /
                ((t.1 + 1 : ℕ) : ℝ))) := by
  have hbitindep : ∀ p i,
      iIndepFun (sampledRaceBitScore Q K beta p i)
        (standardRaceHyperplaneArrayLaw L Pbits d) :=
    fun p i => sampledRaceBitScores_iIndep Q K beta p i
  have hbitmeas : ∀ p i k,
      AEStronglyMeasurable (sampledRaceBitScore Q K beta p i k)
        (standardRaceHyperplaneArrayLaw L Pbits d) :=
    fun p i k => (measurable_sampledRaceBitScore Q K beta p i k).aestronglyMeasurable
  have hbitmean : ∀ p i k,
      ∫ ω, sampledRaceBitScore Q K beta p i k ω
          ∂standardRaceHyperplaneArrayLaw L Pbits d =
        ∫ z, softBitAgreement beta z.2 (rotatedGaussianMargin (alpha p) z)
          ∂standardGaussianPlane :=
    fun p i k => sampledRaceBitScore_integral_eq_planar
      Q K alpha beta p i k (hgeom p)
  have htableindep : ∀ p,
      iIndepFun
        (fun i ω => ∏ k, sampledRaceBitScore Q K beta p i k ω)
        (standardRaceHyperplaneArrayLaw L Pbits d) := by
    intro p
    have hs := sampledRaceTableScores_iIndep (L := L) (Pbits := Pbits) Q K beta p
    have heq : ∀ i : Fin L,
        sampledRaceTableScore (Pbits := Pbits) Q K beta p i =ᵐ[
          standardRaceHyperplaneArrayLaw L Pbits d]
          (fun ω => ∏ k, sampledRaceBitScore Q K beta p i k ω) := by
      intro i
      exact Filter.Eventually.of_forall (fun ω => by rfl)
    exact (iIndepFun_congr heq).1 hs
  have htablemeas : ∀ p i,
      AEMeasurable (fun ω => ∏ k, sampledRaceBitScore Q K beta p i k ω)
        (standardRaceHyperplaneArrayLaw L Pbits d) := by
    intro p i
    exact (Finset.measurable_prod Finset.univ (fun k _ =>
      measurable_sampledRaceBitScore Q K beta p i k)).aemeasurable
  have htablebound : ∀ p i,
      ∀ᵐ ω ∂standardRaceHyperplaneArrayLaw L Pbits d,
        (∏ k, sampledRaceBitScore Q K beta p i k ω) ∈ Set.Icc (0 : ℝ) 1 := by
    intro p i
    exact ae_of_all _ fun ω => by
      change sampledRaceTableScore (Pbits := Pbits) Q K beta p i ω ∈ Set.Icc (0 : ℝ) 1
      exact sampledRaceTableScore_mem_Icc Q K beta p i ω
  have havg_nonneg : ∀ (ω : RaceHyperplaneArray L Pbits d) p,
      0 ≤ causalRaceAverage (sampledRaceBitScore Q K beta) p ω := by
    intro ω p
    simpa [actualCausalRaceAverage] using
      (actualCausalRaceAverage_pos hL Q K beta p ω).le
  have htarget_nonneg : ∀ p,
      0 ≤ causalRaceAngularTarget (Pbits := Pbits) alpha p :=
    fun p => (causalRaceAngularTarget_pos_of_lt_pi alpha halphapi p).le
  have htarget_mass : ∀ t : Fin N,
      0 < ∑ j : Fin (t.1 + 1),
        causalRaceAngularTarget (Pbits := Pbits) alpha
          (⟨t, j⟩ : CausalPair N) :=
    causalRaceAngularTarget_prefix_mass_pos alpha halphapi
  have havg_mass : ∀ (ω : RaceHyperplaneArray L Pbits d) (t : Fin N),
      0 < ∑ j : Fin (t.1 + 1),
        causalRaceAverage (sampledRaceBitScore Q K beta)
          (⟨t, j⟩ : CausalPair N) ω := by
    intro ω t
    simpa [actualCausalRaceAverage] using
      actualCausalRaceAverage_prefix_mass_pos hL Q K beta ω t
  simpa [actualCausalRaceBadSet, actualCausalRaceAverage] using
    (causal_race_high_probability_output_guarantee
      (standardRaceHyperplaneArrayLaw L Pbits d) N hL
      (sampledRaceBitScore Q K beta) alpha beta hbeta halpha0 halphapi
      hbitindep hbitmeas hbitmean htableindep htablemeas htablebound
      V D havg_nonneg htarget_nonneg htarget_mass havg_mass hD hdiam hu)

end RACEFormal
