import RACEFormal.GaussianHardCollisionExpectation
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw

open MeasureTheory ProbabilityTheory WithLp
open scoped ENNReal NNReal RealInnerProductSpace

namespace RACEFormal

/--
Two distinct coordinates of a standard Gaussian Euclidean vector have exactly
the product law of two independent standard real Gaussians.  This is the
coordinate-level model of two orthogonal projections of a Gaussian random
hyperplane.
-/
theorem hasLaw_stdGaussian_coordinate_pair
    {ι : Type*} [Fintype ι]
    (i0 i1 : ι) (hne : i0 ≠ i1) :
    HasLaw (fun x : EuclideanSpace ℝ ι => (x i0, x i1))
      standardGaussianPlane (stdGaussian (EuclideanSpace ℝ ι)) := by
  let γ : Measure ℝ := gaussianReal 0 (1 : NNReal)
  let P : Measure (ι → ℝ) := Measure.pi (fun _ : ι => γ)
  have hcoord : ∀ i : ι, HasLaw (fun x : ι → ℝ => x i) γ P := by
    intro i
    exact MeasurePreserving.hasLaw
      (measurePreserving_eval (fun _ : ι => γ) i)
  have hindAll : iIndepFun (fun i : ι => fun x : ι → ℝ => x i) P := by
    exact iIndepFun_pi (X := fun _ : ι => id) (μ := fun _ : ι => γ)
      (fun _ => aemeasurable_id)
  have hind :
      IndepFun (fun x : ι → ℝ => x i0) (fun x : ι → ℝ => x i1) P :=
    hindAll.indepFun hne
  have hpairRaw :
      HasLaw (fun x : ι → ℝ => (x i0, x i1)) (γ.prod γ) P :=
    hind.hasLaw_prod (hcoord i0) (hcoord i1)
  have hmap :
      P.map (toLp 2) = stdGaussian (EuclideanSpace ℝ ι) := by
    simpa [P, γ] using (map_pi_eq_stdGaussian (ι := ι))
  refine ⟨by fun_prop, ?_⟩
  rw [← hmap, Measure.map_map (by fun_prop) (by fun_prop)]
  simpa [P, γ, standardGaussianPlane, Function.comp_def] using hpairRaw.map_eq

/--
Coordinates in any orthonormal basis of a finite-dimensional real inner-product
space are independent standard Gaussians under `stdGaussian`.  In particular,
two distinct basis coordinates have the same planar law used by the exact
random-hyperplane collision proof.
-/
theorem hasLaw_orthonormal_coordinate_pair
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (b : OrthonormalBasis ι ℝ E)
    (i0 i1 : ι) (hne : i0 ≠ i1) :
    HasLaw (fun x : E => (b.repr x i0, b.repr x i1))
      standardGaussianPlane (stdGaussian E) := by
  have hcoord := hasLaw_stdGaussian_coordinate_pair i0 i1 hne
  refine ⟨by fun_prop, ?_⟩
  change (stdGaussian E).map
      ((fun y : EuclideanSpace ℝ ι => (y i0, y i1)) ∘ b.repr) =
    standardGaussianPlane
  rw [← Measure.map_map (by fun_prop) (by fun_prop), stdGaussian_map]
  exact hcoord.map_eq

/--
A normalized query/key pair is represented in an adapted orthonormal basis by
`q = b i1` and `k = cos(alpha) q - sin(alpha) b i0`.  This is exactly the
2-dimensional span reduction behind Gaussian random-hyperplane hashing.
-/
def IsAngularPairGeometry
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (q k : E) (alpha : ℝ) : Prop :=
  ∃ (b : OrthonormalBasis ι ℝ E) (i0 i1 : ι),
    i0 ≠ i1 ∧
      q = b i1 ∧
      k = Real.cos alpha • b i1 - Real.sin alpha • b i0

/--
For an actual standard-Gaussian random hyperplane in a finite-dimensional
inner-product space, the two projection margins of an angular pair have exactly
the canonical planar representation `(z₂, z₂ cos α - z₁ sin α)` used by the
RACE soft/hard analysis.  Consequently the expected soft one-bit RACE score of
the real projections is exactly the planar expectation already verified above.
-/
theorem gaussian_hyperplane_softBitAgreement_expectation
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (q k : E) (alpha beta : ℝ)
    (hgeom : IsAngularPairGeometry (ι := ι) q k alpha) :
    (∫ r : E, softBitAgreement beta (inner ℝ q r) (inner ℝ k r) ∂(stdGaussian E)) =
      ∫ z, softBitAgreement beta z.2 (rotatedGaussianMargin alpha z)
        ∂standardGaussianPlane := by
  rcases hgeom with ⟨b, i0, i1, hne, hq, hk⟩
  have hpair := hasLaw_orthonormal_coordinate_pair b i0 i1 hne
  let F : ℝ × ℝ → ℝ := fun z =>
    softBitAgreement beta z.2 (rotatedGaussianMargin alpha z)
  have hrot : Measurable (rotatedGaussianMargin alpha) := by
    unfold rotatedGaussianMargin
    fun_prop
  have hpairmap : Measurable (fun z : ℝ × ℝ => (z.2, rotatedGaussianMargin alpha z)) :=
    measurable_snd.prodMk hrot
  have hF : AEStronglyMeasurable F standardGaussianPlane := by
    apply Measurable.aestronglyMeasurable
    change Measurable (fun z : ℝ × ℝ =>
      softBitAgreement beta z.2 (rotatedGaussianMargin alpha z))
    exact (measurable_softBitAgreement_pair beta).comp hpairmap
  have hint := hpair.integral_comp hF
  have hpoint :
      (fun r : E => softBitAgreement beta (inner ℝ q r) (inner ℝ k r)) =
        (fun r : E => F (b.repr r i0, b.repr r i1)) := by
    funext r
    rw [hq, hk]
    simp [F, rotatedGaussianMargin, OrthonormalBasis.repr_apply_apply,
      inner_sub_left, inner_smul_left, mul_comm]
  rw [hpoint]
  simpa [F, Function.comp_def] using hint

end RACEFormal
