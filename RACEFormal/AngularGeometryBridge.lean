import RACEFormal.ActualRaceSampler
import RACEFormal.GaussianHyperplaneSampler
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped RealInnerProductSpace

namespace RACEFormal

/--
The adapted two-dimensional geometry used by the Gaussian proof follows from the
usual unit-vector angular assumptions.  In dimensions at least two, if `q` and
`k` are unit vectors with inner product `cos alpha` and `0 < alpha < π`, then
there is an orthonormal basis in which

`q = b i₁` and `k = cos(alpha) • b i₁ - sin(alpha) • b i₀`.

This discharges `IsAngularPairGeometry` from the natural assumptions appearing
in the RACE angular-kernel formulation.
-/
theorem isAngularPairGeometry_of_unit_inner
    {d : ℕ} (hd : 2 ≤ d)
    (q k : RaceAmbient d) (alpha : ℝ)
    (hq : ‖q‖ = 1) (hk : ‖k‖ = 1)
    (ha0 : 0 < alpha) (hapi : alpha < Real.pi)
    (hinner : inner ℝ q k = Real.cos alpha) :
    IsAngularPairGeometry (ι := Fin d) q k alpha := by
  classical
  have hsin : 0 < Real.sin alpha := Real.sin_pos_of_pos_of_lt_pi ha0 hapi
  have hsin0 : Real.sin alpha ≠ 0 := ne_of_gt hsin
  let e0 : RaceAmbient d :=
    (Real.sin alpha)⁻¹ • (Real.cos alpha • q - k)
  have hq_self : inner ℝ q q = 1 := by
    rw [real_inner_self_eq_norm_sq, hq]
    norm_num
  have hq_e0 : inner ℝ q e0 = 0 := by
    dsimp [e0]
    rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right,
      hq_self, hinner]
    ring
  have he0_q : inner ℝ e0 q = 0 := by
    rw [real_inner_comm]
    exact hq_e0
  have hnum_sq : ‖Real.cos alpha • q - k‖ ^ 2 = Real.sin alpha ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, hq, hk, Real.norm_eq_abs,
      real_inner_smul_left, hinner]
    simp only [mul_one, one_pow, sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq alpha]
  have hnum_nonneg : 0 ≤ ‖Real.cos alpha • q - k‖ := norm_nonneg _
  have hsin_nonneg : 0 ≤ Real.sin alpha := hsin.le
  have hnum_norm : ‖Real.cos alpha • q - k‖ = Real.sin alpha := by
    nlinarith
  have he0_norm : ‖e0‖ = 1 := by
    dsimp [e0]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hsin, hnum_norm]
    exact inv_mul_cancel₀ hsin0
  have hk_repr : k = Real.cos alpha • q - Real.sin alpha • e0 := by
    dsimp [e0]
    rw [smul_smul, mul_inv_cancel₀ hsin0, one_smul]
    abel

  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    norm_num [i0, i1] at this
  let s : Set (Fin d) := {i0, i1}
  let v : Fin d → RaceAmbient d := fun i => if i = i0 then e0 else q
  have hv0 : v i0 = e0 := by simp [v]
  have hv1 : v i1 = q := by simp [v, hi01.symm]
  have hs_orth : Orthonormal ℝ (s.domRestrict v) := by
    constructor
    · intro i
      have hi : i.1 = i0 ∨ i.1 = i1 := by
        have hi' := i.2
        change i.1 = i0 ∨ i.1 = i1 at hi'
        exact hi'
      change ‖v i.1‖ = 1
      rcases hi with hi | hi
      · rw [hi, hv0, he0_norm]
      · rw [hi, hv1, hq]
    · intro a b hab
      have ha : a.1 = i0 ∨ a.1 = i1 := by
        have ha' := a.2
        change a.1 = i0 ∨ a.1 = i1 at ha'
        exact ha'
      have hb : b.1 = i0 ∨ b.1 = i1 := by
        have hb' := b.2
        change b.1 = i0 ∨ b.1 = i1 at hb'
        exact hb'
      change inner ℝ (v a.1) (v b.1) = 0
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exfalso
        apply hab
        apply Subtype.ext
        exact ha.trans hb.symm
      · rw [ha, hb, hv0, hv1]
        exact he0_q
      · rw [ha, hb, hv1, hv0]
        exact hq_e0
      · exfalso
        apply hab
        apply Subtype.ext
        exact ha.trans hb.symm
  have hcard : Module.finrank ℝ (RaceAmbient d) = Fintype.card (Fin d) := by
    simp [RaceAmbient]
  obtain ⟨b, hbext⟩ :=
    hs_orth.exists_orthonormalBasis_extension_of_card_eq hcard
  have hi0s : i0 ∈ s := by simp [s]
  have hi1s : i1 ∈ s := by simp [s]
  have hb0 : b i0 = e0 := by
    rw [hbext i0 hi0s, hv0]
  have hb1 : b i1 = q := by
    rw [hbext i1 hi1s, hv1]
  refine ⟨b, i0, i1, hi01, ?_, ?_⟩
  · exact hb1.symm
  · rw [hb0, hb1]
    exact hk_repr

end RACEFormal
