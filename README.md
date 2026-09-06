# Causal RACE Formalization

Lean 4 / mathlib formalization of a high-probability causal RACE Attention approximation guarantee.

> Independent research. This repository is not an official RACE Attention repository and is not endorsed by the original authors.

## Main result

The top-level concrete theorem is:

```lean
RACEFormal.actual_race_high_probability_output_guarantee
```

It instantiates the abstract causal RACE guarantee with a concrete `L × Pbits` array of independent standard-Gaussian random hyperplanes. The formal chain includes the sampler law, bit/table independence, measurability, score boundedness and positivity, the Gaussian angular collision calculation, finite-temperature soft/hard bias, independent-table concentration, a causal-triangle union bound, and the diameter-sensitive normalized-output bound.

The remaining hypotheses of the concrete theorem are mathematical input conditions rather than hidden sampler assumptions: positive table count, positive soft-hash temperature, nondegenerate angular geometry (`0 < alpha < π` together with `IsAngularPairGeometry`), and value-diameter assumptions.

## Scope

This project verifies the mathematical sampler and theorem. It does **not** prove that a particular CUDA/PyTorch production implementation is bit-for-bit equivalent to the formal model, and it does not substitute for independent expert review or empirical GPU benchmarking.

## Reproduce the check

The project pins Lean 4 and mathlib in `lean-toolchain` and `lakefile.lean`.

```bash
lake update
lake exe cache get
lake build
```

The CI workflow also rejects unfinished proof placeholders in the RACE formalization:

```bash
if grep -R -n -E '\b(sorry|admit|axiom)\b' RACEFormal RACEFormal.lean --include='*.lean'; then
  exit 1
fi
```

## Layout

- `RACEFormal/ActualRaceSampler.lean` — concrete Gaussian random-hyperplane construction.
- `RACEFormal/ActualRaceHypotheses.lean` — sampler measurability, independence, laws, boundedness, and positivity.
- `RACEFormal/GaussianHyperplaneSampler.lean` — Gaussian projection/angle bridge.
- `RACEFormal/SoftmaxProductEquivalence.lean` — equivalence between the explicit corner softmax and factorized form.
- `RACEFormal/CausalRaceEntrywise.lean` — simultaneous causal entrywise guarantee.
- `RACEFormal/FinalCausalRaceGuarantee.lean` — abstract high-probability causal output theorem.
- `RACEFormal/ActualRaceGuarantee.lean` — final concrete theorem with sampler hypotheses discharged.
- `RACEFormal.lean` — imports the complete proof chain so `lake build` checks the full development.

## Provenance

This repository was separated from an unrelated research repository after the causal RACE formalization reached a successful Lean/mathlib kernel check. The migrated `RACEFormal/` tree is byte-for-byte identical to the verified source tree at source commit `6179c07d8cbfedef42af50d1727b341c9431bc05`. The source GitHub Actions verification was run #143, where both `lake build` and the no-placeholder audit succeeded.
