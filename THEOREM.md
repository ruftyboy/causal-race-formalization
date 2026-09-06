# Formal theorem and scope

The strongest paper-facing theorem is:

`RACEFormal.algorithm2_high_probability_output_guarantee_of_unit_vectors`

implemented in `RACEFormal/Algorithm2Corollary.lean`.

The lower-level concrete sampler theorem

`RACEFormal.actual_race_high_probability_output_guarantee`

remains in `RACEFormal/ActualRaceGuarantee.lean` and is used by the stronger corollary.

## What is formalized

The development instantiates the causal RACE guarantee with a concrete mathematical sampler consisting of an `L × Pbits` family of independent standard-Gaussian random hyperplanes. It formalizes the explicit corner-softmax table score, proves its equivalence to the factorized soft-RACE score, establishes the Gaussian random-hyperplane law and angular collision calculation, controls finite-temperature soft/hard bias, proves concentration across independent tables, applies a simultaneous causal-triangle union bound, and completes the deterministic normalization/output step.

The paper-facing theorem is stated from natural geometric inputs. For every causal query/key pair it assumes unit norms and

`inner ℝ q k = cos(alpha)`

with `0 < alpha < π`. In dimension at least two, `RACEFormal.isAngularPairGeometry_of_unit_inner` derives the adapted orthonormal geometry required by the Gaussian proof, so `IsAngularPairGeometry` is no longer an external assumption of the strongest theorem.

For a causal row, outside the explicitly defined bad event, the normalized output error is bounded by a diameter-sensitive term of the form

`D t * min 1 (eps / average_target_mass)`

with

`eps = u + Pbits * twoMarginLeakageBudget beta`.

The theorem also gives an explicit upper bound on the probability of the simultaneous bad event over the full causal triangle.

## Main mathematical inputs that remain assumptions

The strongest theorem retains genuine problem inputs rather than sampler-construction obligations. In particular it assumes:

- dimension `d ≥ 2`;
- positive table count `L > 0`;
- positive soft-hash temperature/scale `beta`;
- unit query and key vectors;
- pair angles satisfying `0 < alpha < π`;
- the angular relation `inner ℝ q k = cos(alpha)`;
- nonnegative value-diameter bounds and the corresponding pairwise value-diameter condition;
- a nonnegative concentration tolerance `u`.

Sampler-specific measurability, Gaussian laws, within-table bit independence, across-table independence, score boundedness, positive realized normalization mass, positive target mass, relevant expectation identities, and the adapted angular geometry are discharged inside the Lean development.

## Published Algorithm-2 notation

`RACEFormal.algorithm2TableScore` is written literally as the sum over RACE corners of the product of query and key corner-softmax probabilities. `algorithm2CausalAverage`, `algorithm2CausalNumerator`, `algorithm2CausalDenominator`, and `algorithm2CausalOutput` expose the causal estimator in normalized `Num/Den` form. The formalization proves the explicit corner-softmax table score is equal to the factorized sampled score used internally by the theorem chain.

## Verification

The repository is built with Lean 4 and mathlib using the pinned versions in `lean-toolchain` and `lakefile.lean`.

Run:

```bash
lake update
lake exe cache get
lake build
```

GitHub Actions additionally rejects any Lean source containing `sorry`, `admit`, or an explicit `axiom` placeholder, and CI runs automatically on pushes to `main` as well as pull requests.

## What this does not establish

This formalization proves a theorem about the mathematical causal RACE sampler and the Algorithm-2-style normalized estimator represented in Lean. It does **not** by itself prove that a particular CUDA, PyTorch, Triton, or other production implementation is bit-for-bit or semantically equivalent to the formal model. Implementation-specific normalization order, stabilizing epsilons, finite-precision arithmetic, RNG behavior, and fused-kernel details require a separate correspondence proof or test harness.

It also does not establish empirical speedups, memory savings, model-quality preservation, or production usefulness. Those require separate implementation and benchmarking work.

This repository is independent research and is not an official RACE repository.
