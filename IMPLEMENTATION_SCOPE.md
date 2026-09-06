# Published Algorithm 2 versus current upstream implementation

This formalization targets the mathematical causal RACE estimator described by the published Algorithm 2: each table supplies a query/key soft-bucket inner-product score, the table contributions are aggregated into a causal numerator and denominator, and the final output is the globally normalized `Num_t / Den_t` estimator.

The Lean development now exposes this notation explicitly in `RACEFormal/Algorithm2Corollary.lean`.

## Upstream code snapshot audited

The current `main` branch of `sahiljoshi515/RACE_Attention` was audited at commit:

`87219986b515ad77a865709186c8888f9a7a17b3`

Its shared causal reference path in `scaling/race_common.py` computes the same Gaussian projections and corner softmax probabilities, but the prefix/output stage is written as

```python
A_pref = probsK.cumsum(dim=1)
B_pref = (probsK.unsqueeze(-1) * V2.unsqueeze(2)).cumsum(dim=1)
E_pref = B_pref / (A_pref.unsqueeze(-1) + eps)
out = torch.einsum("nts,ntsd->ntd", probsQ, E_pref)
```

The older `misc/race.py::BatchedACE` path has the same structural choice: it normalizes each bucket prefix by its own mass (with an added numerical epsilon) before mixing those bucket means with the query probabilities.

That is generally not algebraically identical to the globally normalized published Algorithm-2 estimator proved here. In particular, bucketwise normalization and global numerator/denominator normalization do not commute in general, and the implementation also adds a positive numerical epsilon.

## What is formally connected to the implementation

The Lean development does formally establish the following mathematical correspondences:

- the sampler is an `L × Pbits` array of independent standard-Gaussian hyperplanes, matching the distributional meaning of `torch.randn(L, Kbits, d)`;
- the literal corner logits `beta * tanh(Wx)^T v` are modeled;
- the explicit `2^Pbits` corner softmax is proved exactly equivalent to the product-form binary representation used by the proof;
- `beta = 1 / sqrt(d)` is proved to reproduce the current implementation's `tanh(proj) / sqrt(d)` logit scaling.

These statements concern the sampler and soft-hash score construction. They do **not** prove equivalence of the current bucketwise-normalized causal scan to the globally normalized Algorithm-2 output theorem.

## Claim boundary

Accordingly, the correct claim is:

> The Lean theorem verifies the concrete Gaussian mathematical sampler and the published globally normalized causal Algorithm-2 estimator, under its stated input assumptions.

It should **not** be stated that the current CUDA/PyTorch implementation is formally verified by this repository.

A production-code correspondence result would require either:

1. a separate theorem for the current bucketwise-prefix-normalized estimator, including its numerical epsilon, or
2. an implementation path that computes the published global `Num_t / Den_t` estimator and a semantics/parity bridge from that code to the Lean model.
