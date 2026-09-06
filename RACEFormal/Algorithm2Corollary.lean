import RACEFormal.AngularGeometryBridge
import RACEFormal.ActualRaceGuarantee
import RACEFormal.SoftmaxProductEquivalence

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace RACEFormal

/--
One published-Algorithm-2 table score written literally as the inner product of
the query and key corner-softmax distributions.
-/
noncomputable def algorithm2TableScore
    {N L Pbits d : ℕ}
    (Q K : Fin N → RaceAmbient d) (beta : ℝ)
    (p : CausalPair N) (table : Fin L)
    (ω : RaceHyperplaneArray L Pbits d) : ℝ :=
  ∑ v : RaceCorner Pbits,
    raceCornerSoftmax beta (fun bit => ω (table, bit)) (Q p.1) v *
      raceCornerSoftmax beta (fun bit => ω (table, bit))
        (K (causalPairKeyIndex p)) v

/-- The literal corner-softmax table score equals the factorized sampled score. -/
theorem algorithm2TableScore_eq_sampledRaceTableScore
    {N L Pbits d : ℕ}
    (Q K : Fin N → RaceAmbient d) (beta : ℝ)
    (p : CausalPair N) (table : Fin L)
    (ω : RaceHyperplaneArray L Pbits d) :
    algorithm2TableScore Q K beta p table ω =
      sampledRaceTableScore (Pbits := Pbits) Q K beta p table ω := by
  unfold algorithm2TableScore
  rw [explicitCornerSoftmaxKernel_eq_raceSoftTableKernel]
  exact (sampledRaceTableScore_eq_kernel Q K beta p table ω).symm

/-- The per-pair score obtained by averaging the `L` literal Algorithm-2 table scores. -/
noncomputable def algorithm2CausalAverage
    {N L Pbits d : ℕ}
    (Q K : Fin N → RaceAmbient d) (beta : ℝ)
    (p : CausalPair N) (ω : RaceHyperplaneArray L Pbits d) : ℝ :=
  (L : ℝ)⁻¹ * ∑ table : Fin L, algorithm2TableScore Q K beta p table ω

/-- The literal Algorithm-2 average is exactly the average used by the concrete theorem. -/
@[simp] theorem algorithm2CausalAverage_eq_actualCausalRaceAverage
    {N L Pbits d : ℕ}
    (Q K : Fin N → RaceAmbient d) (beta : ℝ)
    (p : CausalPair N) (ω : RaceHyperplaneArray L Pbits d) :
    algorithm2CausalAverage Q K beta p ω =
      actualCausalRaceAverage (L := L) (Pbits := Pbits) Q K beta p ω := by
  unfold algorithm2CausalAverage actualCausalRaceAverage causalRaceAverage
  congr 1
  apply Finset.sum_congr rfl
  intro table _
  rw [algorithm2TableScore_eq_sampledRaceTableScore]
  rfl

/-- Simultaneous bad event stated directly with literal Algorithm-2 corner-softmax scores. -/
def algorithm2CausalBadSet
    {N L Pbits d : ℕ}
    (Q K : Fin N → RaceAmbient d) (alpha : CausalPair N → ℝ)
    (beta eps : ℝ) : Set (RaceHyperplaneArray L Pbits d) :=
  ⋃ p : CausalPair N,
    {ω | eps ≤ |algorithm2CausalAverage (L := L) (Pbits := Pbits) Q K beta p ω -
      causalRaceAngularTarget (Pbits := Pbits) alpha p|}

@[simp] theorem algorithm2CausalBadSet_eq_actualCausalRaceBadSet
    {N L Pbits d : ℕ}
    (Q K : Fin N → RaceAmbient d) (alpha : CausalPair N → ℝ)
    (beta eps : ℝ) :
    algorithm2CausalBadSet (L := L) (Pbits := Pbits) Q K alpha beta eps =
      actualCausalRaceBadSet (L := L) (Pbits := Pbits) Q K alpha beta eps := by
  ext ω
  simp [algorithm2CausalBadSet, actualCausalRaceBadSet, causalRaceBadSet,
    actualCausalRaceAverage]

/-- Algorithm-2 denominator after exchanging the finite sums over tables and prefix keys. -/
noncomputable def algorithm2CausalDenominator
    {N L Pbits d : ℕ}
    (Q K : Fin N → RaceAmbient d) (beta : ℝ)
    (t : Fin N) (ω : RaceHyperplaneArray L Pbits d) : ℝ :=
  ∑ j : Fin (t.1 + 1),
    algorithm2CausalAverage (L := L) (Pbits := Pbits) Q K beta
      (⟨t, j⟩ : CausalPair N) ω

/-- Algorithm-2 numerator after exchanging the finite sums over tables and prefix keys. -/
noncomputable def algorithm2CausalNumerator
    {E : Type*} {N L Pbits d : ℕ}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q K : Fin N → RaceAmbient d) (beta : ℝ)
    (V : (t : Fin N) → Fin (t.1 + 1) → E)
    (t : Fin N) (ω : RaceHyperplaneArray L Pbits d) : E :=
  ∑ j : Fin (t.1 + 1),
    algorithm2CausalAverage (L := L) (Pbits := Pbits) Q K beta
      (⟨t, j⟩ : CausalPair N) ω • V t j

/--
Published Algorithm-2 output, written as `Num_t / Den_t` in normalized-kernel
form.  The next lemma records the literal inverse-denominator-times-numerator
identity.
-/
noncomputable def algorithm2CausalOutput
    {E : Type*} {N L Pbits d : ℕ}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q K : Fin N → RaceAmbient d) (beta : ℝ)
    (V : (t : Fin N) → Fin (t.1 + 1) → E)
    (t : Fin N) (ω : RaceHyperplaneArray L Pbits d) : E :=
  ∑ j : Fin (t.1 + 1),
    (algorithm2CausalAverage (L := L) (Pbits := Pbits) Q K beta
        (⟨t, j⟩ : CausalPair N) ω /
      algorithm2CausalDenominator (L := L) (Pbits := Pbits) Q K beta t ω) • V t j

/-- The normalized-kernel expression is exactly `Den_t⁻¹ • Num_t`. -/
theorem algorithm2CausalOutput_eq_inv_smul_numerator
    {E : Type*} {N L Pbits d : ℕ}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q K : Fin N → RaceAmbient d) (beta : ℝ)
    (V : (t : Fin N) → Fin (t.1 + 1) → E)
    (t : Fin N) (ω : RaceHyperplaneArray L Pbits d) :
    algorithm2CausalOutput (L := L) (Pbits := Pbits) Q K beta V t ω =
      (algorithm2CausalDenominator (L := L) (Pbits := Pbits) Q K beta t ω)⁻¹ •
        algorithm2CausalNumerator (L := L) (Pbits := Pbits) Q K beta V t ω := by
  unfold algorithm2CausalOutput algorithm2CausalNumerator
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul]
  congr 1
  rw [div_eq_mul_inv, mul_comm]

/-- Exact normalized powered-angular target output for one causal row. -/
noncomputable def causalAngularTargetOutput
    {E : Type*} {N Pbits : ℕ}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (alpha : CausalPair N → ℝ)
    (V : (t : Fin N) → Fin (t.1 + 1) → E)
    (t : Fin N) : E :=
  ∑ j : Fin (t.1 + 1),
    (causalRaceAngularTarget (Pbits := Pbits) alpha
        (⟨t, j⟩ : CausalPair N) /
      (∑ i : Fin (t.1 + 1),
        causalRaceAngularTarget (Pbits := Pbits) alpha
          (⟨t, i⟩ : CausalPair N))) • V t j

/--
Concrete causal RACE guarantee stated from the natural paper-level assumptions:
unit query/key vectors, their angular inner products, the literal corner
softmax, and the published Algorithm-2 `Num/Den` output.
-/
theorem algorithm2_high_probability_output_guarantee_of_unit_vectors
    {E : Type*} {N L Pbits d : ℕ}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hd : 2 ≤ d) (hL : 0 < L)
    (Q K : Fin N → RaceAmbient d)
    (hQunit : ∀ t, ‖Q t‖ = 1)
    (hKunit : ∀ j, ‖K j‖ = 1)
    (alpha : CausalPair N → ℝ)
    (beta : ℝ) (hbeta : 0 < beta)
    (halpha0 : ∀ p, 0 < alpha p)
    (halphapi : ∀ p, alpha p < Real.pi)
    (hinner : ∀ p,
      inner ℝ (Q p.1) (K (causalPairKeyIndex p)) = Real.cos (alpha p))
    (V : (t : Fin N) → Fin (t.1 + 1) → E)
    (D : Fin N → ℝ)
    (hD : ∀ t, 0 ≤ D t)
    (hdiam : ∀ t j k, ‖V t j - V t k‖ ≤ D t)
    {u : ℝ} (hu : 0 ≤ u) :
    let B := (Pbits : ℝ) * twoMarginLeakageBudget beta
    let eps := u + B
    (standardRaceHyperplaneArrayLaw L Pbits d).real
        (algorithm2CausalBadSet (L := L) (Pbits := Pbits)
          Q K alpha beta eps)
      ≤ (Fintype.card (CausalPair N) : ℝ) *
        (2 * Real.exp (-((L : ℝ) * u) ^ 2 /
          (2 * (∑ _i : Fin L, ((1 / 2 : ℝ≥0) ^ 2) : ℝ≥0)))) ∧
      ∀ ω, ω ∉ algorithm2CausalBadSet (L := L) (Pbits := Pbits)
          Q K alpha beta eps → ∀ t : Fin N,
        ‖algorithm2CausalOutput (L := L) (Pbits := Pbits) Q K beta V t ω -
            causalAngularTargetOutput (Pbits := Pbits) alpha V t‖
          ≤ D t * min 1
            (eps /
              ((∑ i : Fin (t.1 + 1),
                  causalRaceAngularTarget (Pbits := Pbits) alpha
                    (⟨t, i⟩ : CausalPair N)) /
                ((t.1 + 1 : ℕ) : ℝ))) := by
  have hgeom : ∀ p, IsAngularPairGeometry (ι := Fin d)
      (Q p.1) (K (causalPairKeyIndex p)) (alpha p) := by
    intro p
    exact isAngularPairGeometry_of_unit_inner hd
      (Q p.1) (K (causalPairKeyIndex p)) (alpha p)
      (hQunit p.1) (hKunit (causalPairKeyIndex p))
      (halpha0 p) (halphapi p) (hinner p)
  have hbase := actual_race_high_probability_output_guarantee
    (E := E) (Pbits := Pbits) hL Q K alpha beta hbeta halpha0 halphapi hgeom
    V D hD hdiam hu
  dsimp only at hbase ⊢
  constructor
  · simpa using hbase.1
  · intro ω hgood t
    have hgood' : ω ∉ actualCausalRaceBadSet (L := L) (Pbits := Pbits)
        Q K alpha beta (u + (Pbits : ℝ) * twoMarginLeakageBudget beta) := by
      simpa using hgood
    have hrow := hbase.2 ω hgood' t
    have hout :
        algorithm2CausalOutput (L := L) (Pbits := Pbits) Q K beta V t ω -
            causalAngularTargetOutput (Pbits := Pbits) alpha V t =
          ∑ j : Fin (t.1 + 1),
            (algorithm2CausalAverage (L := L) (Pbits := Pbits) Q K beta
                (⟨t, j⟩ : CausalPair N) ω /
                algorithm2CausalDenominator (L := L) (Pbits := Pbits)
                  Q K beta t ω -
              causalRaceAngularTarget (Pbits := Pbits) alpha
                  (⟨t, j⟩ : CausalPair N) /
                (∑ i : Fin (t.1 + 1),
                  causalRaceAngularTarget (Pbits := Pbits) alpha
                    (⟨t, i⟩ : CausalPair N))) • V t j := by
      unfold algorithm2CausalOutput causalAngularTargetOutput
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [sub_smul]
    rw [hout]
    simpa [algorithm2CausalDenominator] using hrow

end RACEFormal
