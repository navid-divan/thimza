# $\textsf{Thimza}$

$\textsf{Thimza}$ is a three-round $(t,n)$ lattice threshold signature whose signatures are
[Raccoon](https://doi.org/10.1007/978-3-031-68376-3_13) signatures, accepted by the unmodified Raccoon verifier, which measured on non-terrestrial networks via [LEOScope](https://leoscope.surrey.ac.uk/) [[Details](https://dl.acm.org/doi/10.1145/3750832.3750835)]. To see quickly how $\textsf{Thimza}$ works, refer to [Scheme.md](https://github.com/navid-divan/thimza/blob/main/docs/Scheme.md) and for concrete security parameters see [Parameters.md](https://github.com/navid-divan/thimza/blob/main/docs/Parameters.md) file. This repository contains our practical developments, findings and results, as this table shows the layout:
| Path | Content |
| --- | --- |
| [`docs/Draft.pdf`](docs/Draft.pdf) | full version of our research, with all proofs and the details |
| [`thimza/`](thimza) | implementation of $\textsf{Thimza}$ and of the schemes it is compared with |
| [`experiments/`](experiments) | correctness test, benchmarks, parameter derivation and figures |
| [`results/`](results), [`figures/`](figures) | outputs of the experiments |
| [`easycrypt-proofs/`](easycrypt-proofs) | [EasyCrypt](https://doi.org/10.1007/978-3-642-22792-9_5) machine-checked proofs with QROM modelled as in [EasyPQC](https://dl.acm.org/doi/10.1145/3460120.3484567), see [README](easycrypt-proofs/README.md) |
| [`NTN_Experiment-LEOScope/`](NTN_Experiment-LEOScope) | container tested on [LEOScope](https://leoscope.surrey.ac.uk/) and the artifacts it returned, see [README](NTN_Experiment-LEOScope/README.md) |

⚠️ **This is an ongoing initiative, so $\textsf{Thimza}$ should not be deployed in real-world production systems yet.**

## Implementation
`ring.py` implements negacyclic NTT arithmetic over $\mathbb{Z}_q[X]/(X^{\varphi}+1)$ for $q<2^{51}$,
`sampling.py` the uniform, discrete Gaussian, challenge and monomial samplers, `prf.py` the
[SHAKE256](https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-208.pdf)-based XOF, PRF, hash to challenge and hash to Gaussian, `shamir.py` [Shamir](https://dl.acm.org/doi/10.1145/359168.359176) sharing over
$R_q$ with Lagrange reconstruction, `masking.py` the antisymmetric masks of $\textsf{Thimza}$ and the
ordered pair masks of prior work, `core.py` the [Raccoon](https://doi.org/10.1007/978-3-031-68376-3_13) core shared by all Fiat-Shamir schemes,
`estimator.py` a core-SVP estimator (primal uSVP and primal SIS) inspired by the [Lattice
Estimator](https://github.com/malb/lattice-estimator), `derive.py` the parameter constraint system and the size model, and `params.py` the
parameter sets of all implemented schemes and level. `schemes/` contains $\textsf{Thimza}$ and the
comparison schemes. Ring elements are `uint64` coefficient arrays. Modular multiplication uses a floating point
quotient followed by a wrap-around 64bit reduction, which is precise for all primes $q<2^{51}$ and
is validated against negacyclic multiplication.

### Experiments 
The benchmarks codes requires Python $\ge3.9$, NumPy $\ge1.24$ and Matplotlib $\ge3.5$
(`pip install -r requirements.txt`).
```
python3 experiments/run_all.py            # correctness and benchmarks
python3 experiments/correctness_bound.py  # numerical check of the verification bound
python3 experiments/derive_params.py      # parameter derivation and validation
python3 experiments/make_figures.py       # show the results as figures
```
* `run_all.py` runs the signing protocol of every scheme for
  $`(t,n)\in\{(2,3),(3,5),(4,6),(5,8),(7,10)\}`$, verifies the signatures (with the unmodified
  Raccoon verifier for the schemes that are interchangeable with Raccoon), measures the cost of
  every round per signer for $t$ from $2$ to $1024$, and writes `results/correctness.json` and
  `results/bench.json`.
* `derive_params.py` validates the estimator against [Kyber](https://ieeexplore.ieee.org/document/8406610) and [Dilithium](https://tches.iacr.org/index.php/TCHES/article/view/839), re-derives the
  published parameter set of [Ringtail](https://ieeexplore.ieee.org/document/11023447) from the constraint system, and prints the $\textsf{Thimza}$
  parameter sets.
* `correctness_bound.py` samples the aggregated nonce, the aggregated noise, the truncation
  perturbation and the key rounding residue from their precise distributions and compares the
  largest signature norm with the verification bound $B$.
* `make_figures.py` reads the results and writes the results as figures into `figures/`.

## License
This project and its implementation are released under the Apache License 2.0.
