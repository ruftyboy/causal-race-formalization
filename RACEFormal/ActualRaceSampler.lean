import RACEFormal.SoftRaceBit
import RACEFormal.CornerFactorization
import RACEFormal.CausalTriangle
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace RACEFormal

/-- Ambient Euclidean space used by one RACE attention head. -/
abbrev RaceAmbient (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- One Gaussian random hyperplane normal. -/
abbrev RaceHyperplane (d : ℕ) := RaceAmbient d

/-- Indices of the random hyperplanes in `L` tables with `Pbits` planes per table. -/
abbrev RacePlaneIndex (L Pbits : ℕ) := Fin L × Fin Pbits

/-- A complete draw of the random hyperplanes used by RACE. -/
abbrev RaceHyperplaneArray (L Pbits d : ℕ) :=
  RacePlaneIndex L Pbits → RaceHyperplane d

/-- The law `N(0,I_d)` of one random hyperplane normal. -/
noncomputable def standardRaceHyperplaneLaw (d : ℕ) : Measure (RaceHyperplane d) :=
  stdGaussian (RaceHyperplane d)

/--
The actual RACE sampler: every `(table, bit)` hyperplane is drawn independently
from `N(0,I_d)`.  This is the measure-theoretic counterpart of
`torch.randn(L, Pbits, d)` in the reference implementation.
-/
noncomputable def standardRaceHyperplaneArrayLaw (L Pbits d : ℕ) :
    Measure (RaceHyperplaneArray L Pbits d) :=
  Measure.pi (fun _ : RacePlaneIndex L Pbits => standardRaceHyperplaneLaw d)

instance standardRaceHyperplaneLaw_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (standardRaceHyperplaneLaw d) := by
  unfold standardRaceHyperplaneLaw
  infer_instance

instance standardRaceHyperplaneArrayLaw_isProbabilityMeasure (L Pbits d : ℕ) :
    IsProbabilityMeasure (standardRaceHyperplaneArrayLaw L Pbits d) := by
  unfold standardRaceHyperplaneArrayLaw
  infer_instance

/-- Every sampled plane has exactly the standard multivariate Gaussian law. -/
theorem raceHyperplane_hasLaw
    (L Pbits d : ℕ) (idx : RacePlaneIndex L Pbits) :
    HasLaw (fun ω : RaceHyperplaneArray L Pbits d => ω idx)
      (standardRaceHyperplaneLaw d)
      (standardRaceHyperplaneArrayLaw L Pbits d) := by
  refine ⟨(measurable_pi_apply idx).aemeasurable, ?_⟩
  unfold standardRaceHyperplaneArrayLaw
  exact (measurePreserving_eval
    (fun _ : RacePlaneIndex L Pbits => standardRaceHyperplaneLaw d) idx).map_eq

/-- All hyperplane normals in the complete RACE draw are mutually independent. -/
theorem raceHyperplanes_iIndep
    (L Pbits d : ℕ) :
    iIndepFun
      (fun idx (ω : RaceHyperplaneArray L Pbits d) => ω idx)
      (standardRaceHyperplaneArrayLaw L Pbits d) := by
  unfold standardRaceHyperplaneArrayLaw
  exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

/-- Within any fixed table, the `Pbits` Gaussian hyperplanes are independent. -/
theorem raceTableHyperplanes_iIndep
    (L Pbits d : ℕ) (table : Fin L) :
    iIndepFun
      (fun bit (ω : RaceHyperplaneArray L Pbits d) => ω (table, bit))
      (standardRaceHyperplaneArrayLaw L Pbits d) := by
  have hg : Function.Injective (fun bit : Fin Pbits => (table, bit)) := by
    intro a b h
    exact congrArg Prod.snd h
  exact iIndepFun.precomp hg (raceHyperplanes_iIndep L Pbits d)

/-- Gaussian random-hyperplane projection `wᵀx`. -/
noncomputable def raceProjection {d : ℕ}
    (w x : RaceAmbient d) : ℝ :=
  inner ℝ w x

/-- Boolean encoding of a hypercube corner coordinate as `{-1,+1}`. -/
def raceCornerSign (b : Bool) : ℝ := if b then 1 else -1

/-- The `2^Pbits` corners used by the RACE soft hash. -/
abbrev RaceCorner (Pbits : ℕ) := Fin Pbits → Bool

/--
The exact Algorithm-1/2 corner logit
`β * tanh(Wx)ᵀ v`, with a Boolean representation of `v ∈ {-1,+1}^P`.
-/
noncomputable def raceCornerLogit {d Pbits : ℕ}
    (beta : ℝ) (planes : Fin Pbits → RaceHyperplane d)
    (x : RaceAmbient d) (v : RaceCorner Pbits) : ℝ :=
  beta * ∑ bit, Real.tanh (raceProjection (planes bit) x) * raceCornerSign (v bit)

/-- Unnormalized exponential weight of one RACE hypercube corner. -/
noncomputable def raceCornerWeight {d Pbits : ℕ}
    (beta : ℝ) (planes : Fin Pbits → RaceHyperplane d)
    (x : RaceAmbient d) (v : RaceCorner Pbits) : ℝ :=
  Real.exp (raceCornerLogit beta planes x v)

/-- Softmax partition function over all `2^Pbits` corners. -/
noncomputable def raceCornerPartition {d Pbits : ℕ}
    (beta : ℝ) (planes : Fin Pbits → RaceHyperplane d)
    (x : RaceAmbient d) : ℝ :=
  ∑ v : RaceCorner Pbits, raceCornerWeight beta planes x v

/-- The actual soft bucket probability from Algorithm 1/2. -/
noncomputable def raceCornerSoftmax {d Pbits : ℕ}
    (beta : ℝ) (planes : Fin Pbits → RaceHyperplane d)
    (x : RaceAmbient d) (v : RaceCorner Pbits) : ℝ :=
  raceCornerWeight beta planes x v / raceCornerPartition beta planes x

/-- The RACE softmax partition function is strictly positive. -/
theorem raceCornerPartition_pos {d Pbits : ℕ}
    (beta : ℝ) (planes : Fin Pbits → RaceHyperplane d)
    (x : RaceAmbient d) :
    0 < raceCornerPartition beta planes x := by
  let v0 : RaceCorner Pbits := fun _ => false
  have hterm : 0 < raceCornerWeight beta planes x v0 := by
    exact Real.exp_pos _
  have hle : raceCornerWeight beta planes x v0 ≤
      ∑ v : RaceCorner Pbits, raceCornerWeight beta planes x v := by
    exact Finset.single_le_sum
      (fun v _ => (Real.exp_pos (raceCornerLogit beta planes x v)).le)
      (Finset.mem_univ v0)
  exact lt_of_lt_of_le hterm hle

/-- The explicit hypercube softmax is a probability distribution. -/
theorem raceCornerSoftmax_mass_one {d Pbits : ℕ}
    (beta : ℝ) (planes : Fin Pbits → RaceHyperplane d)
    (x : RaceAmbient d) :
    (∑ v : RaceCorner Pbits, raceCornerSoftmax beta planes x v) = 1 := by
  rw [show (∑ v : RaceCorner Pbits, raceCornerSoftmax beta planes x v) =
      (∑ v : RaceCorner Pbits, raceCornerWeight beta planes x v) /
        raceCornerPartition beta planes x by
      simp [raceCornerSoftmax, Finset.sum_div]]
  exact div_self (ne_of_gt (raceCornerPartition_pos beta planes x))

/-- Every explicit soft-hash bucket probability is nonnegative. -/
theorem raceCornerSoftmax_nonneg {d Pbits : ℕ}
    (beta : ℝ) (planes : Fin Pbits → RaceHyperplane d)
    (x : RaceAmbient d) (v : RaceCorner Pbits) :
    0 ≤ raceCornerSoftmax beta planes x v := by
  unfold raceCornerSoftmax raceCornerWeight
  exact div_nonneg (Real.exp_pos _).le (raceCornerPartition_pos beta planes x).le

/--
Product-form binary representation of the same soft-hash family.  This is the
representation used by the existing one-bit bias analysis and exposes the
independence across the `Pbits` Gaussian rows.
-/
noncomputable def raceProductCornerFeature {d Pbits : ℕ}
    (beta : ℝ) (planes : Fin Pbits → RaceHyperplane d)
    (x : RaceAmbient d) (v : RaceCorner Pbits) : ℝ :=
  ∏ bit, softBitProb beta (raceProjection (planes bit) x) (v bit)

/-- The product-form corner feature is normalized exactly. -/
theorem raceProductCornerFeature_mass_one {d Pbits : ℕ}
    (beta : ℝ) (planes : Fin Pbits → RaceHyperplane d)
    (x : RaceAmbient d) :
    (∑ v : RaceCorner Pbits, raceProductCornerFeature beta planes x v) = 1 := by
  simpa [raceProductCornerFeature] using
    (product_corner_mass_one Pbits
      (fun bit b => softBitProb beta (raceProjection (planes bit) x) b)
      (fun bit => softBitProb_mass_one beta (raceProjection (planes bit) x)))

/-- One table's soft RACE pair score, as an inner product over all corners. -/
noncomputable def raceSoftTableKernel {d Pbits : ℕ}
    (beta : ℝ) (planes : Fin Pbits → RaceHyperplane d)
    (q k : RaceAmbient d) : ℝ :=
  ∑ v : RaceCorner Pbits,
    raceProductCornerFeature beta planes q v *
      raceProductCornerFeature beta planes k v

/--
The full `2^Pbits` corner inner product factors exactly into the product of the
`Pbits` one-hyperplane soft agreement scores.
-/
theorem raceSoftTableKernel_eq_bitProduct {d Pbits : ℕ}
    (beta : ℝ) (planes : Fin Pbits → RaceHyperplane d)
    (q k : RaceAmbient d) :
    raceSoftTableKernel beta planes q k =
      ∏ bit, softBitAgreement beta
        (raceProjection (planes bit) q)
        (raceProjection (planes bit) k) := by
  simpa [raceSoftTableKernel, raceProductCornerFeature, softBitAgreement] using
    (product_corner_inner_factorization Pbits
      (fun bit b => softBitProb beta (raceProjection (planes bit) q) b)
      (fun bit b => softBitProb beta (raceProjection (planes bit) k) b))

/-- The global key position represented by a causal prefix index. -/
def causalPairKeyIndex {N : ℕ} (pair : CausalPair N) : Fin N :=
  ⟨pair.2.1,
    lt_of_le_of_lt (Nat.le_of_lt_succ pair.2.2) pair.1.2⟩

/-- The actual sampled one-bit soft score for a causal pair and a table/bit row. -/
noncomputable def sampledRaceBitScore
    {N L Pbits d : ℕ}
    (Q K : Fin N → RaceAmbient d) (beta : ℝ)
    (pair : CausalPair N) (table : Fin L) (bit : Fin Pbits)
    (ω : RaceHyperplaneArray L Pbits d) : ℝ :=
  softBitAgreement beta
    (raceProjection (ω (table, bit)) (Q pair.1))
    (raceProjection (ω (table, bit)) (K (causalPairKeyIndex pair)))

/-- The actual sampled table score obtained from the shared Gaussian hyperplane matrix. -/
noncomputable def sampledRaceTableScore
    {N L Pbits d : ℕ}
    (Q K : Fin N → RaceAmbient d) (beta : ℝ)
    (pair : CausalPair N) (table : Fin L)
    (ω : RaceHyperplaneArray L Pbits d) : ℝ :=
  ∏ bit, sampledRaceBitScore Q K beta pair table bit ω

/-- The sampled table score is definitionally the factorized corner kernel. -/
theorem sampledRaceTableScore_eq_kernel
    {N L Pbits d : ℕ}
    (Q K : Fin N → RaceAmbient d) (beta : ℝ)
    (pair : CausalPair N) (table : Fin L)
    (ω : RaceHyperplaneArray L Pbits d) :
    sampledRaceTableScore Q K beta pair table ω =
      raceSoftTableKernel beta (fun bit => ω (table, bit))
        (Q pair.1) (K (causalPairKeyIndex pair)) := by
  rw [raceSoftTableKernel_eq_bitProduct]
  rfl

end RACEFormal
