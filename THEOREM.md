# Formal theorem and scope

The top-level concrete theorem is:

`RACEFormal.actual_race_high_probability_output_guarantee`

implemented in `RACEFormal/ActualRaceGuarantee.lean`.

## What is formalized

The development instantiates the causal RACE guarantee with a concrete mathematical sampler consisting of an `L × Pbits` family of independent standard-Gaussian random hyperplanes. It formalizes the soft RACE table score, the Gaussian random-hyperplane law, the angular collision calculation, finite-temperature soft/hard bias, concentration across independent tables, a simultaneous causal-triangle union bound, and the deterministic normalization/output step.

For a causal row, outside the explicitly defined bad event, the normalized output error is bounded by a diameter-sensitive term of the form

`D t * min 1 (eps / average_target_mass)`

with

`eps = u + Pbits * twoMarginLeakageBudget beta`.

The theorem also gives an explicit upper bound on the probability of the simultaneous bad event over the full causal triangle.

## Main mathematical inputs that remain assumptions

The final concrete theorem retains genuine input conditions rather than sampler-construction obligations. In particular it assumes:

- `L > 0`;
- positive soft-hash temperature/scale `beta`;
- pair angles satisfying `0 < alpha < π`;
- `IsAngularPairGeometry` for each query/key pair, connecting the pair to the normalized angular geometry used by the Gaussian calculation;
- nonnegative value-diameter bounds and the corresponding pairwise value-diameter condition;
- a nonnegative concentration tolerance `u`.

The sampler-specific measurability, Gaussian laws, within-table bit independence, across-table independence, score boundedness, positive realized normalization mass, positive target mass, and relevant expectation identities are discharged inside the Lean development.

## Verification

The repository is built with Lean 4 and mathlib using the pinned versions in `lean-toolchain` and `lakefile.lean`.

Run:

```bash
lake update
lake exe cache get
lake build
```

The GitHub Actions workflow additionally rejects any Lean source containing `sorry`, `admit`, or an explicit `axiom` placeholder.

## What this does not establish

This formalization proves a theorem about the mathematical causal RACE sampler represented in Lean. It does **not** by itself prove that a particular CUDA, PyTorch, Triton, or other production implementation is bit-for-bit or semantically equivalent to the formal model. It also does not establish empirical speedups, memory savings, model-quality preservation, or production usefulness. Those require separate implementation correspondence and empirical evaluation.

This repository is independent research and is not an official RACE repository.
