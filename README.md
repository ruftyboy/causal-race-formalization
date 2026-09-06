# Causal RACE Formalization

Lean 4 / mathlib formalization of a high-probability causal RACE Attention approximation guarantee.

> Independent research. This repository is not an official RACE Attention repository and is not endorsed by the original authors.

## Main result

The strongest paper-facing theorem is:

```lean
RACEFormal.algorithm2_high_probability_output_guarantee_of_unit_vectors
```

It states the guarantee directly from natural angular assumptions: query/key vectors are unit vectors, their inner product is `cos(alpha)`, `0 < alpha < π`, the soft-hash temperature is positive, and the causal value vectors satisfy a diameter bound. In dimension at least two, the development derives the adapted two-dimensional geometry used by the Gaussian proof rather than assuming it separately.

The theorem is written in explicit published-Algorithm-2 notation. Each table score is the inner product of the query and key corner-softmax distributions; the causal estimator is the normalized `Num/Den` output obtained from the averaged table scores. It instantiates the proof with a concrete `L × Pbits` array of independent standard-Gaussian random hyperplanes.

The formal chain includes:

- the concrete Gaussian sampler law;
- within-table bit independence and across-table independence;
- measurability, boundedness, and positivity of the sampled scores;
- equivalence between explicit corner softmax and the factorized soft-RACE score;
- the exact Gaussian random-hyperplane angular collision calculation;
- finite-temperature soft/hard bias;
- independent-table concentration;
- a simultaneous causal-triangle union bound;
- deterministic normalization stability and the diameter-sensitive output bound;
- a derivation of `IsAngularPairGeometry` from unit-vector + inner-product assumptions.

The earlier theorem

```lean
RACEFormal.actual_race_high_probability_output_guarantee
```

remains as the lower-level concrete sampler theorem used by the paper-facing corollary.

## Verification status

The project is kernel-checked by Lean 4/mathlib. GitHub Actions runs `lake build` and separately rejects Lean source containing `sorry`, `admit`, or an explicit `axiom` placeholder. CI runs on pull requests, manual dispatches, and pushes to `main`.

## Scope and implementation correspondence

This project verifies the mathematical causal RACE sampler and the published Algorithm-2-style normalized estimator represented in Lean. It does **not** prove that a particular CUDA, PyTorch, Triton, or other production implementation is bit-for-bit or semantically equivalent to this formal model.

In particular, implementation-specific normalization order, stabilizing epsilons, floating-point behavior, RNG details, or kernel fusion are outside the theorem unless separately connected to the Lean definitions. Empirical speedups, memory savings, model-quality preservation, and production usefulness also require separate experiments.

## Reproduce the check

The project pins Lean 4 and mathlib in `lean-toolchain` and `lakefile.lean`.

```bash
lake update
lake exe cache get
lake build
```

The CI placeholder audit is:

```bash
if grep -R -n -E '\b(sorry|admit|axiom)\b' RACEFormal RACEFormal.lean --include='*.lean'; then
  exit 1
fi
```

## Layout

- `RACEFormal/ActualRaceSampler.lean` — concrete Gaussian random-hyperplane construction.
- `RACEFormal/ActualRaceHypotheses.lean` — sampler measurability, independence, laws, boundedness, and positivity.
- `RACEFormal/GaussianHyperplaneSampler.lean` — Gaussian projection/angle bridge.
- `RACEFormal/AngularGeometryBridge.lean` — derives the adapted angular geometry from unit-vector and inner-product assumptions.
- `RACEFormal/SoftmaxProductEquivalence.lean` — equivalence between explicit corner softmax and factorized soft-RACE form.
- `RACEFormal/CausalRaceEntrywise.lean` — simultaneous causal entrywise guarantee.
- `RACEFormal/FinalCausalRaceGuarantee.lean` — abstract high-probability causal output theorem.
- `RACEFormal/ActualRaceGuarantee.lean` — concrete sampler theorem with sampler hypotheses discharged.
- `RACEFormal/Algorithm2Corollary.lean` — paper-facing unit-vector / explicit Algorithm-2 theorem.
- `RACEFormal.lean` — imports the complete proof chain so `lake build` checks the full development.

## Provenance

The repository was separated from an unrelated research repository after the original causal RACE formalization reached a successful Lean/mathlib kernel check. The original migrated `RACEFormal/` tree matched source commit `6179c07d8cbfedef42af50d1727b341c9431bc05`, whose GitHub Actions run #143 passed both `lake build` and the no-placeholder audit. Subsequent public-repository commits strengthen the theorem while retaining CI verification.
