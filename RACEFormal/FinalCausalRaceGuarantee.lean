import RACEFormal.CausalRaceEntrywise
import RACEFormal.RowGuarantee

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace RACEFormal

/-- The `L`-table averaged factorized soft-RACE score for a causal pair. -/
noncomputable def causalRaceAverage
    {Ω : Type*} {N L Pbits : ℕ}
    (W : CausalPair N → Fin L → Fin Pbits → Ω → ℝ)
    (p : CausalPair N) (ω : Ω) : ℝ :=
  (L : ℝ)⁻¹ * ∑ i, ∏ k, W p i k ω

/-- The exact powered angular collision target for a causal pair. -/
noncomputable def causalRaceAngularTarget
    {N Pbits : ℕ} (alpha : CausalPair N → ℝ)
    (p : CausalPair N) : ℝ :=
  (1 - alpha p / Real.pi) ^ Pbits

/-- The simultaneous causal-triangle failure event at radius `eps`. -/
def causalRaceBadSet
    {Ω : Type*} {N L Pbits : ℕ}
    (W : CausalPair N → Fin L → Fin Pbits → Ω → ℝ)
    (alpha : CausalPair N → ℝ) (eps : ℝ) : Set Ω :=
  ⋃ p : CausalPair N,
    {ω | eps ≤ |causalRaceAverage W p ω -
      causalRaceAngularTarget (Pbits := Pbits) alpha p|}

/--
Outside the simultaneous entrywise failure event, every causal row inherits
the diameter-sensitive normalized-output guarantee.
-/
theorem causal_race_row_output_of_good_event
    {Ω E : Type*} {N L Pbits : ℕ}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : CausalPair N → Fin L → Fin Pbits → Ω → ℝ)
    (alpha : CausalPair N → ℝ)
    (eps : ℝ) (heps : 0 ≤ eps)
    (V : (t : Fin N) → Fin (t.1 + 1) → E)
    (D : Fin N → ℝ)
    (havg_nonneg : ∀ (ω : Ω) p, 0 ≤ causalRaceAverage W p ω)
    (htarget_nonneg : ∀ p,
      0 ≤ causalRaceAngularTarget (Pbits := Pbits) alpha p)
    (htarget_mass : ∀ t : Fin N,
      0 < ∑ j : Fin (t.1 + 1),
        causalRaceAngularTarget (Pbits := Pbits) alpha
          (⟨t, j⟩ : CausalPair N))
    (havg_mass : ∀ (ω : Ω) (t : Fin N),
      0 < ∑ j : Fin (t.1 + 1),
        causalRaceAverage W (⟨t, j⟩ : CausalPair N) ω)
    (hD : ∀ t, 0 ≤ D t)
    (hdiam : ∀ t j k, ‖V t j - V t k‖ ≤ D t)
    {ω : Ω} (hgood : ω ∉ causalRaceBadSet W alpha eps)
    (t : Fin N) :
    ‖∑ j : Fin (t.1 + 1),
        (causalRaceAverage W (⟨t, j⟩ : CausalPair N) ω /
            (∑ i : Fin (t.1 + 1),
              causalRaceAverage W (⟨t, i⟩ : CausalPair N) ω) -
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
  let a : Fin (t.1 + 1) → ℝ := fun j =>
    causalRaceAngularTarget (Pbits := Pbits) alpha
      (⟨t, j⟩ : CausalPair N)
  let b : Fin (t.1 + 1) → ℝ := fun j =>
    causalRaceAverage W (⟨t, j⟩ : CausalPair N) ω
  have hentry : ∀ j, |b j - a j| ≤ eps := by
    intro j
    have hnot : ω ∉
        {ω | eps ≤
          |causalRaceAverage W (⟨t, j⟩ : CausalPair N) ω -
            causalRaceAngularTarget (Pbits := Pbits) alpha
              (⟨t, j⟩ : CausalPair N)|} := by
      intro hj
      apply hgood
      exact Set.mem_iUnion.mpr ⟨(⟨t, j⟩ : CausalPair N), hj⟩
    have hlt :
        |causalRaceAverage W (⟨t, j⟩ : CausalPair N) ω -
          causalRaceAngularTarget (Pbits := Pbits) alpha
            (⟨t, j⟩ : CausalPair N)| < eps :=
      lt_of_not_ge hnot
    simpa [a, b] using hlt.le
  have h := bias_variance_to_output_bound_average_mass
    (m := t.1 + 1) (E := E) (Nat.succ_pos t.1)
    a a b (V t) (D t) eps 0
    (fun j => htarget_nonneg (⟨t, j⟩ : CausalPair N))
    (fun j => havg_nonneg ω (⟨t, j⟩ : CausalPair N))
    (by simpa [a] using htarget_mass t)
    (by simpa [b] using havg_mass ω t)
    (hD t) heps (le_refl 0)
    (hdiam t)
    hentry
    (fun j => by simp [a])
  simpa [a, b] using h

/--
Final high-probability causal RACE output theorem.

The first conjunct is the simultaneous probability bound over the whole causal
triangle.  The second says that on every sample outside that failure event,
every causal row satisfies the normalized diameter-sensitive output bound.
Thus finite-temperature bias, independent-table concentration, the causal
union bound, and deterministic normalization are assembled in one theorem.
-/
theorem causal_race_high_probability_output_guarantee
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) {L Pbits : ℕ} (hL : 0 < L)
    (W : CausalPair N → Fin L → Fin Pbits → Ω → ℝ)
    (alpha : CausalPair N → ℝ)
    (beta : ℝ) (hbeta : 0 < beta)
    (halpha0 : ∀ p, 0 < alpha p)
    (halphapi : ∀ p, alpha p < Real.pi)
    (hbitindep : ∀ p i, iIndepFun (W p i) μ)
    (hbitmeas : ∀ p i k, AEStronglyMeasurable (W p i k) μ)
    (hbitmean : ∀ p i k,
      ∫ ω, W p i k ω ∂μ =
        ∫ z, softBitAgreement beta z.2 (rotatedGaussianMargin (alpha p) z)
          ∂standardGaussianPlane)
    (htableindep : ∀ p,
      iIndepFun (fun i ω => ∏ k, W p i k ω) μ)
    (htablemeas : ∀ p i,
      AEMeasurable (fun ω => ∏ k, W p i k ω) μ)
    (htablebound : ∀ p i,
      ∀ᵐ ω ∂μ, (∏ k, W p i k ω) ∈ Set.Icc (0 : ℝ) 1)
    (V : (t : Fin N) → Fin (t.1 + 1) → E)
    (D : Fin N → ℝ)
    (havg_nonneg : ∀ (ω : Ω) p, 0 ≤ causalRaceAverage W p ω)
    (htarget_nonneg : ∀ p,
      0 ≤ causalRaceAngularTarget (Pbits := Pbits) alpha p)
    (htarget_mass : ∀ t : Fin N,
      0 < ∑ j : Fin (t.1 + 1),
        causalRaceAngularTarget (Pbits := Pbits) alpha
          (⟨t, j⟩ : CausalPair N))
    (havg_mass : ∀ (ω : Ω) (t : Fin N),
      0 < ∑ j : Fin (t.1 + 1),
        causalRaceAverage W (⟨t, j⟩ : CausalPair N) ω)
    (hD : ∀ t, 0 ≤ D t)
    (hdiam : ∀ t j k, ‖V t j - V t k‖ ≤ D t)
    {u : ℝ} (hu : 0 ≤ u) :
    let B := (Pbits : ℝ) * twoMarginLeakageBudget beta
    let eps := u + B
    μ.real (causalRaceBadSet W alpha eps)
        ≤ (Fintype.card (CausalPair N) : ℝ) *
          (2 * Real.exp (-((L : ℝ) * u) ^ 2 /
            (2 * (∑ _i : Fin L, ((1 / 2 : ℝ≥0) ^ 2) : ℝ≥0)))) ∧
      ∀ ω, ω ∉ causalRaceBadSet W alpha eps → ∀ t : Fin N,
        ‖∑ j : Fin (t.1 + 1),
            (causalRaceAverage W (⟨t, j⟩ : CausalPair N) ω /
                (∑ i : Fin (t.1 + 1),
                  causalRaceAverage W (⟨t, i⟩ : CausalPair N) ω) -
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
  dsimp only
  constructor
  · simpa [causalRaceBadSet, causalRaceAverage, causalRaceAngularTarget] using
      (causal_race_factorized_entrywise_union_bound
        μ N hL W alpha beta hbeta halpha0 halphapi
        hbitindep hbitmeas hbitmean htableindep htablemeas htablebound hu)
  · have hB : 0 ≤ (Pbits : ℝ) * twoMarginLeakageBudget beta := by
      unfold twoMarginLeakageBudget
      positivity
    have heps : 0 ≤ u + (Pbits : ℝ) * twoMarginLeakageBudget beta :=
      add_nonneg hu hB
    intro ω hgood t
    exact causal_race_row_output_of_good_event
      W alpha (u + (Pbits : ℝ) * twoMarginLeakageBudget beta) heps
      V D havg_nonneg htarget_nonneg htarget_mass havg_mass hD hdiam hgood t

end RACEFormal
