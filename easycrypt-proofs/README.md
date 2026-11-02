# $\textsf{Thimza}$ machine-checked security proofs

This directory formalizes $\textsf{Thimza}$ and its security argument in [EasyCrypt](https://link.springer.com/chapter/10.1007/978-3-642-22792-9_5). 

## Running the check

The proof requires EasyCrypt r2025.03 ([codebase](https://github.com/EasyCrypt/easycrypt)) or later with an SMT backend configured
(Alt-Ergo and Z3 are the ones used here). If `easycrypt` is not on the `PATH`
the script falls back to `~/.opam/easycrypt/bin/easycrypt`. To facilitate the assessing process, you can simply use our script to run all:
```
./check.sh
```
The script scans the sources for skipped proofs, compiles all sixteen files
with EasyCrypt in dependency order, times each one, and prints a summary. It
exits with status 0 only if every proof checks and no forbidden tactic is
present.

## Trusted base

Every axiom of the development is in one of three places, and `check.sh` fails if an
axiom appears anywhere else.

* **Quantum random oracle facts.** `QROM.ec` contains the abstract theories `QROM` and
  `QROMLazy`, and `ExtRO.ec` the abstract theory `ExtRO`. Their axioms are
  * `pr_col`: finding a collision with `q` queries succeeds with probability at most
    `27 (q + 2)^3 p_max` (Zhandry, CRYPTO 2019, as used in EasyPQC);
  * `ghhm`: adaptively reprogramming `nr` points, each drawn from a distribution of the
    adversary with largest probability at most `p`, is noticed with advantage at most
    `nr (sqrt(q p) + q p / 2)` (Grilo, Hövelmanns, Hülsing, Majenz, ASIACRYPT 2021);
  * `o2h_lazy`: answering commitments with a lazily sampled function and programming the
    oracle at a committed point only when its secret is revealed is noticed with advantage
    at most `2 q sqrt(nu p) + nu^2 p`, for `nu` secrets whose openings take each value with
    probability at most `p` (one way to hiding of Ambainis, Hamburg, Unruh, CRYPTO 2019);
  * `ext_sim` and `ext_sound`: the extractable simulator of Don, Fehr, Majenz, Schaffner
    (EUROCRYPT 2022) changes the view by at most `8 l (q + l) sqrt(2 p_max)`, and an
    accepted opening differs from the extracted one with probability at most
    `8 l (q + 1) sqrt(2 p_max) + (40 e^2 (q + l + 1)^3 + 2) p_max`.

  Each is a published theorem for quantum adversaries whose bound also holds for classical
  ones, so the theories are consistent with the classical semantics of EasyCrypt. The other
  axioms of these theories are their parameters (the output distribution is lossless and
  uniform, the domain is finite, the simulator state starts lossless); they are discharged
  when the theory is cloned, except the simulator parameter, which is part of the
  specification of the extractor.
* **Modelling axioms on abstract parameters.** `ChainBase.ec` states that the abstract
  distributions of nonces, noise, keys, first messages, digests and challenges are lossless,
  the last three uniform, and that messages and digest inputs form finite types.
* **Hypotheses of the game chain.** The lemmas of the chain are proved in sections whose
  `declare axiom`s become hypotheses of the closed lemmas: the adversary terminates
  (`A_ll`) and respects the query bounds `qh0`, `qh1`, `qhc`, `qsig` (`A_bnd`), the
  encoding of the inputs of `H1` is injective on well formed requests (`e1_inj`), and the
  openings `rndc (A r + e')` take each value with probability at most `pw` (`reg_open`,
  the regularity lemma of the paper).

The ring is the concrete quotient `Zp[X]/(X^phi + 1)` of the EasyCrypt library, vectors and
matrices are subtypes of functions declared with `subtype`, and every clone of a library
theory ends with `proof *`. The only clones that keep axioms are the four instances of the
oracle theories in `ChainBase.ec`, which keep exactly the quantum facts.

## Modelling of the quantum random oracle

We follow EasyPQC (Barbosa et al., ACM CCS 2021) as
every random oracle is a function sampled in one go from `dfun`; adversaries reach an
oracle only through its procedure, and no proof step inspects or logs one of their queries;
query counters are classical and every fact assumes a query bound given as a Hoare
judgement. The challenger's own classical evaluations are logged where a collision bound
needs them. The lemmas `dfh_reprog` (reprogramming one point keeps the oracle uniform) and
`dfh_split` (oracles on the two parts of a partition combine to one oracle) are proved
from the definition of `dfun`.

## The game chain

`ChainBase.ec` instantiates the oracles (`H0H` for first messages of honest parties, with
lazy commitments, `H0C` for corrupt indices, with extraction, `H1O` for digests and `HCO`
for challenges) and defines the adversary interface with query counters. The chain starts
from the game `G0` of `ChainGame.ec`, which is TS-UF-4 in the opening semantics played
with Thimza: corruption, key generation with Shamir shares, pair seeds, the three signing
oracles with all their checks and erasure, and verification of the forgery.

| Hop | File | Lemma | Cost |
|---|---|---|---|
| G0 to G1: random functions for honest pairs | `ChainGame.ec` | `hop_prf` | PRF advantage of `B1` |
| collisions of digests and first messages | `ChainCol.ec` | `col1_bound`, `col0_bound` | `27 (qh1 + 2 qsig + 2)^3 p_max`, `27 (qh0 + (t + 1) qsig + 2)^3 p_max` |
| G1 to G1s: responses without honest pair values | `ChainSim.ec` | `o3_sim`, `run_sim`, `g1_g1s` | digest collision bound |
| G1s to G1t: unused pair values dropped | `ChainDead.ec` | `g1s_g1t` | 0 |
| G1t to lazy first messages | `ChainLazy.ec` | `g1t_lazy0`, `bl_cnt`, `g1t_lazy` | `2 (qh0 + t qsig) sqrt(qsig pw) + qsig^2 pw` |

In `G1s` the third round never reads an honest pair value: a response is uniform while
another honest member of the request has not responded, and otherwise it closes the sum,
exactly as in the view partition lemma of the paper; a second response of a party under the
same request reuses the stored offset. The invariant of `o3_sim` relates the stored offsets
to the masks of the first game, and `fresh_key` shows that the mask of the designated
partner is fresh unless two digests collide. This is the hop to `G7` of the paper, which
needs only distinct digests and so comes earlier in the development.

The hops that use extraction (`ext_sim`, `ext_sound`), reprogramming (`ghhm`), the hint
embedding, the Shamir translation and HintMLWE are proved in our paper; their algebraic
cores are mechanized (`hint_commit`, `honest_aggregate`, `final_reduction`), but their
composition with the chain is not yet mechanized.

