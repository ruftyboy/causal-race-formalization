import RACEFormal.AngularDisagreement
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.Fourier.AddCircle

open Set Metric MeasureTheory

namespace RACEFormal

noncomputable section

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The sine function descended directly to the additive circle of circumference `2π`.
Using `AddCircle` directly keeps the standard measurable and Haar-measure instances aligned. -/
def circleSin (theta : AddCircle (2 * Real.pi)) : ℝ :=
  Real.sin_periodic.lift theta

@[simp]
theorem circleSin_mk (x : ℝ) :
    circleSin (QuotientAddGroup.mk x : AddCircle (2 * Real.pi)) = Real.sin x :=
  rfl

@[continuity, fun_prop]
theorem continuous_circleSin : Continuous circleSin :=
  Real.continuous_sin.quotient_liftOn' _

/--
The strict sign-disagreement event for two sine halfspaces whose angular
separation is `alpha`, represented on the standard additive circle.
-/
def strictCircleSineDisagreement (alpha : ℝ) : Set (AddCircle (2 * Real.pi)) :=
  ({theta | 0 < circleSin theta} ∩
      {theta | circleSin (theta - QuotientAddGroup.mk alpha) < 0}) ∪
    ({theta | circleSin theta < 0} ∩
      {theta | 0 < circleSin (theta - QuotientAddGroup.mk alpha)})

/-- The strict disagreement event is Borel measurable. -/
theorem measurableSet_strictCircleSineDisagreement (alpha : ℝ) :
    MeasurableSet (strictCircleSineDisagreement alpha) := by
  have hshift : Continuous (fun theta : AddCircle (2 * Real.pi) =>
      circleSin (theta - QuotientAddGroup.mk alpha)) :=
    continuous_circleSin.comp (continuous_id.sub continuous_const)
  unfold strictCircleSineDisagreement
  exact (((isOpen_lt continuous_const continuous_circleSin).inter
      (isOpen_lt hshift continuous_const)).union
    ((isOpen_lt continuous_circleSin continuous_const).inter
      (isOpen_lt continuous_const hshift))).measurableSet

/-- Casting a real angle to the additive circle gives the corresponding real sine inequalities. -/
theorem mk_mem_strictCircleSineDisagreement_iff (alpha x : ℝ) :
    ((QuotientAddGroup.mk x : AddCircle (2 * Real.pi)) ∈
        strictCircleSineDisagreement alpha) ↔
      ((0 < Real.sin x ∧ Real.sin (x - alpha) < 0) ∨
        (Real.sin x < 0 ∧ 0 < Real.sin (x - alpha))) := by
  simp [strictCircleSineDisagreement, circleSin, ← QuotientAddGroup.mk_sub]

/--
On the canonical representative interval `(-π, π]`, strict opposite sine signs
occur exactly on the two open angular arcs of total length `2 * alpha`.
-/
theorem real_strict_circle_sine_disagreement_iff
    (alpha x : ℝ) (ha0 : 0 < alpha) (hapi : alpha < Real.pi)
    (hx : x ∈ Set.Ioc (-Real.pi) Real.pi) :
    ((0 < Real.sin x ∧ Real.sin (x - alpha) < 0) ∨
        (Real.sin x < 0 ∧ 0 < Real.sin (x - alpha))) ↔
      x ∈ canonicalStrictSignDisagreementIntervals alpha := by
  unfold canonicalStrictSignDisagreementIntervals
  constructor
  · rintro (h | h)
    · left
      have hx0 : 0 < x := by
        by_contra hnot
        have hxle : x ≤ 0 := le_of_not_gt hnot
        have hsle := Real.sin_nonpos_of_nonpos_of_neg_pi_le hxle hx.1.le
        linarith
      have hyneg : x - alpha < 0 := by
        by_contra hnot
        have hy0 : 0 ≤ x - alpha := le_of_not_gt hnot
        have hypi : x - alpha ≤ Real.pi := by linarith [hx.2, ha0]
        have hsge := Real.sin_nonneg_of_nonneg_of_le_pi hy0 hypi
        linarith
      exact ⟨hx0, by linarith⟩
    · right
      have hxneg : x < 0 := by
        by_contra hnot
        have hx0 : 0 ≤ x := le_of_not_gt hnot
        have hsge := Real.sin_nonneg_of_nonneg_of_le_pi hx0 hx.2
        linarith
      have hyneg : x - alpha < 0 := by linarith
      have hylt : x - alpha < -Real.pi := by
        by_contra hnot
        have hyge : -Real.pi ≤ x - alpha := le_of_not_gt hnot
        have hsle := Real.sin_nonpos_of_nonpos_of_neg_pi_le hyneg.le hyge
        linarith
      exact ⟨hx.1, by linarith⟩
  · rintro (h | h)
    · left
      have hxpi : x < Real.pi := lt_trans h.2 hapi
      have hsx : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi h.1 hxpi
      have hyneg : x - alpha < 0 := by linarith [h.2]
      have hynpi : -Real.pi < x - alpha := by linarith [h.1, hapi]
      exact ⟨hsx, Real.sin_neg_of_neg_of_neg_pi_lt hyneg hynpi⟩
    · right
      have hxneg : x < 0 := by linarith [h.2, hapi]
      have hsx : Real.sin x < 0 :=
        Real.sin_neg_of_neg_of_neg_pi_lt hxneg h.1
      let y : ℝ := x - alpha
      have hylo : -2 * Real.pi < y := by
        dsimp [y]
        linarith [h.1, hapi]
      have hyhi : y < -Real.pi := by
        dsimp [y]
        linarith [h.2]
      have hz0 : 0 < y + 2 * Real.pi := by linarith
      have hzpi : y + 2 * Real.pi < Real.pi := by linarith
      have hzs : 0 < Real.sin (y + 2 * Real.pi) :=
        Real.sin_pos_of_pos_of_lt_pi hz0 hzpi
      have hys : 0 < Real.sin y := by
        simpa using hzs
      exact ⟨hsx, by simpa [y] using hys⟩

/-- The strict canonical disagreement arcs lie inside `(-π, π]`. -/
theorem canonicalStrictSignDisagreementIntervals_subset_Ioc_circle
    (alpha : ℝ) (hapi : alpha < Real.pi) :
    canonicalStrictSignDisagreementIntervals alpha ⊆
      Set.Ioc (-Real.pi) Real.pi := by
  intro x hx
  simp only [canonicalStrictSignDisagreementIntervals, Set.mem_union,
    Set.mem_Ioo] at hx
  rcases hx with hx | hx
  · constructor
    · linarith [Real.pi_pos, hx.1]
    · exact (hx.2.trans hapi).le
  · constructor
    · exact hx.1
    · linarith [hx.2, hapi, Real.pi_pos]

/-- Pulling the circle event back to the canonical real interval gives exactly the two arcs. -/
theorem projection_preimage_strictCircleSineDisagreement
    (alpha : ℝ) (ha0 : 0 < alpha) (hapi : alpha < Real.pi) :
    (QuotientAddGroup.mk ⁻¹' strictCircleSineDisagreement alpha ∩
        Set.Ioc (-Real.pi) Real.pi) =
      canonicalStrictSignDisagreementIntervals alpha := by
  ext x
  change (((QuotientAddGroup.mk x : AddCircle (2 * Real.pi)) ∈
      strictCircleSineDisagreement alpha ∧
      x ∈ Set.Ioc (-Real.pi) Real.pi) ↔
    x ∈ canonicalStrictSignDisagreementIntervals alpha)
  constructor
  · rintro ⟨hdis, hx⟩
    exact (real_strict_circle_sine_disagreement_iff alpha x ha0 hapi hx).1
      ((mk_mem_strictCircleSineDisagreement_iff alpha x).1 hdis)
  · intro hdis
    have hx := canonicalStrictSignDisagreementIntervals_subset_Ioc_circle alpha hapi hdis
    refine ⟨(mk_mem_strictCircleSineDisagreement_iff alpha x).2 ?_, hx⟩
    exact (real_strict_circle_sine_disagreement_iff alpha x ha0 hapi hx).2 hdis

/--
Exact unnormalized angular measure of strict random-hyperplane sign disagreement.
The additive circle has circumference `2π`, and the disagreement arcs have total length `2α`.
-/
theorem volume_strictCircleSineDisagreement
    (alpha : ℝ) (ha0 : 0 < alpha) (hapi : alpha < Real.pi) :
    (volume : Measure (AddCircle (2 * Real.pi)))
        (strictCircleSineDisagreement alpha) = ENNReal.ofReal (2 * alpha) := by
  have hproj :=
    AddCircle.add_projection_respects_measure (T := 2 * Real.pi) (-Real.pi)
      (measurableSet_strictCircleSineDisagreement alpha)
  have hend : -Real.pi + 2 * Real.pi = Real.pi := by ring
  have hproj' :
      (volume : Measure (AddCircle (2 * Real.pi)))
          (strictCircleSineDisagreement alpha) =
        volume (QuotientAddGroup.mk ⁻¹' strictCircleSineDisagreement alpha ∩
          Set.Ioc (-Real.pi) Real.pi) := by
    simpa [hend] using hproj
  calc
    (volume : Measure (AddCircle (2 * Real.pi)))
        (strictCircleSineDisagreement alpha)
        = volume (QuotientAddGroup.mk ⁻¹' strictCircleSineDisagreement alpha ∩
            Set.Ioc (-Real.pi) Real.pi) := hproj'
    _ = volume (canonicalStrictSignDisagreementIntervals alpha) := by
      rw [projection_preimage_strictCircleSineDisagreement alpha ha0 hapi]
    _ = ENNReal.ofReal (2 * alpha) :=
      volume_canonicalStrictSignDisagreementIntervals alpha ha0.le hapi.le

/--
Under normalized Haar measure on the angle circle, strict sign disagreement has
probability exactly `alpha / π` for `0 < alpha < π`.
-/
theorem haarReal_strictCircleSineDisagreement
    (alpha : ℝ) (ha0 : 0 < alpha) (hapi : alpha < Real.pi) :
    (@AddCircle.haarAddCircle (2 * Real.pi) _).real
        (strictCircleSineDisagreement alpha) = alpha / Real.pi := by
  have hvol := volume_strictCircleSineDisagreement alpha ha0 hapi
  have hvolReal :
      (volume : Measure (AddCircle (2 * Real.pi))).real
          (strictCircleSineDisagreement alpha) = 2 * alpha := by
    rw [Measure.real, hvol, ENNReal.toReal_ofReal]
    linarith
  rw [AddCircle.volume_eq_smul_haarAddCircle,
    measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal] at hvolReal
  · apply (eq_div_iff Real.pi_ne_zero).2
    nlinarith [hvolReal]
  · positivity

end

end RACEFormal
