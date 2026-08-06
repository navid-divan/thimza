# $\textsf{Thimza}$

As a post-quantum threshold signature scheme, $\textsf{Thimza}$ is a threshold system from lattices. This repo contains $\textsf{Thimza}$'s **(i) [core implementation](#core-implementation)** for evaluation and **(ii) [construction specification](https://github.com/navid-divan/thimza/tree/main/docs)**, along with its **(iii) [machine-checked proofs](https://github.com/navid-divan/thimza/tree/main/easycrypt-proofs)**. As this is an ongoing initiative, the detailes of both codes and [EasyCrypt](https://link.springer.com/chapter/10.1007/978-3-642-22792-9_5) proofs are being updated and evolving. 



## Core Implementation

The files in this proof-of-concept directory includes `ring.py` for negacyclic NTT arithmetic over $Z_q[X]/(X^phi+1)$, $q < 2^51$, `sampling.py` for uniform, discrete Gaussian, challenge and monomial samplers, `prf.py` for SHAKE256-based XOF, PRF, hash-to-challenge, hash-to-Gaussian, `shamir.py` for Shamir sharing over $R_q$ and Lagrange reconstruction, `masking.py` for antisymmetric ($\textsf{Thimza}$) and ordered-pair (prior works) masking, `core.py` for the [Raccoon](https://link.springer.com/chapter/10.1007/978-3-031-68376-3_13) core shared by all Fiat-Shamir schemes, `estimator.py` for a small core-SVP estimator (primal uSVP and primal SIS) inspired by the [Lattice Estimator](https://github.com/malb/lattice-estimator), `derive.py` for the parameter constraint system and the size model, `params.py` parameter sets for every implemented scheme and level.



## Evaluating Benchmark

To run the prototype code, it requires `python` >= 3.9, `numpy`  >= 1.24, and `matplotlib` >= 3.5. 

```
python3 experiments/run_all.py            # correctness + benchmark, ~2 minutes
python3 experiments/correctness_bound.py  # numerical check of Theorem 5.2
python3 experiments/derive_params.py      # parameter derivation and validation
python3 experiments/make_figures.py       # all EPS figures
```

`run_all.py` writes `results/correctness.json` and `results/bench.json`.
`make_figures.py` reads them and writes EPS outputs into `figures/` directory for assessing comparison.

## Procedure Check

`run_all.py` executes the signing protocol of all six schemes for
$(t,n)$ in ${(2,3),(3,5),(4,6),(5,8),(7,10)}$ and verifies resulting
signatures. For the five interchangeable schemes the verifier used is the
unmodified [Raccoon](https://link.springer.com/chapter/10.1007/978-3-031-68376-3_13) verifier, which is the operational content of functional
interchangeability. It then measures the cost of every protocol round per signer
for thresholds from 2 to 1024.

`derive_params.py` validates the estimator against [Kyber](https://ieeexplore.ieee.org/document/8406610) and [Dilithium](https://github.com/pq-crystals/dilithium), then
re-derives the published parameter set of [Ringtail](https://ieeexplore.ieee.org/document/11023447) from the constraint system,
which it reproduces and finally prints the $\textsf{Thimza}$ parameter sets and the
two-round design space.

`correctness_bound.py` draws the aggregated randomness, the aggregated noise, the
commitment truncation perturbation and the key rounding residue from their exact
distributions and shows the largest observed signature norm against the
verification bound.

## Arithmetic backend

Ring elements are stored as `uint64` coefficient arrays. Modular multiplication
uses a floating point quotient followed by a wrap-around 64-bit reduction, which
is exact for every prime $q < 2^51$; this is validated against
negacyclic multiplication for both ring degrees used in our draft. The forward
and inverse transforms are vectorized.

## Licence

This repo's project and its underlying implementation are released under the Apache License 2.0.

