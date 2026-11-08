# Machine-checked Security Proofs of $\textsf{Thimza}$

This directory formalizes $\textsf{Thimza}$ and its security argument in [EasyCrypt](https://link.springer.com/chapter/10.1007/978-3-642-22792-9_5), with the quantum random oracle modelled as in [EasyPQC](https://dl.acm.org/doi/10.1145/3460120.3484567). 

## Running the check

The proof requires EasyCrypt r2025.03 ([codebase](https://github.com/EasyCrypt/easycrypt)) or later with an SMT backend configured. Run

```
./check.sh
```
which removes every cached result (`*.eco`), scans for `admit`, compiles the files in
dependency order, and prints a summary of the trusted base. The current summary is 774 proved statements, checked in about fifteen minutes, with no `admit` and no global axiom outside the trusted base below.

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

## Modelling of the Quantum Random Oracle

We follow EasyPQC (Barbosa et al. ACM CCS 2021):
every random oracle is a function sampled in one go from `dfun`; adversaries reach an
oracle only through its procedure, and no proof step inspects or logs one of their queries;
query counters are classical and every fact assumes a query bound given as a Hoare
judgement. The challenger's own classical evaluations are logged where a collision bound
needs them. The lemmas `dfh_reprog` (reprogramming one point keeps the oracle uniform) and
`dfh_split` (oracles on the two parts of a partition combine to one oracle) are proved
from the definition of `dfun`.

## The Game Chain

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

The chain continues through the remaining hops of our research paper, all mechanized:

| Hop | File | Lemma | Cost |
|---|---|---|---|
| lazy game to game with flags `b1`, `b2`, `b3` | `ChainFlag.ec` | `gl_ga`, `ga_split` | `Pr[b1] + Pr[b2] + Pr[b3]` |
| extraction of corrupt first messages | `ChainExt.ec` | `ga_ext` | the `ext_sim` and `ext_sound` terms |
| reprogramming of the challenge at completed requests | `ChainRep.ec` | `ge_rep` | `qsig (sqrt(qc pw2) + qc pw2 / 2)` (`ghhm`) |
| explicit programming | `ChainProg.ec` | `rep_gp` | 0 |
| responses computed from hints, up to the flag `bH` | `ChainHint.ec` | `gp_gh` | `Pr[GP: bH]` |
| `bH` only with `bP` or `bC` (consistency of the run) | `ChainCons.ec` | `gp_cons`, `gp_split` | `Pr[GP: bP or bC]` |
| Shamir translation, HintMLWE, SelfTargetMSIS | `ShamirHide.ec`, `ChainFin.ec` | `gh_hm`, `hm_stm`, `gh_bound` | HintMLWE advantage of `B2` + STMSIS success of `B3` |

Bounds of the flags, all mechanized:

| Flag | File | Lemma | Bound |
|---|---|---|---|
| `bC` (completion beyond the budget) | `ChainPB.ec` | `gp_bc_pr` | 0 |
| `bP` (a point programmed twice) | `ChainPB.ec` | `gp_bp` | `qsig^2 pw2` |
| `b2` (fresh first message equal to an existing one) | `ChainGA.ec`, `ChainB2.ec` | `ga_b2` | `qsig (1 + t) qsig p_max(dcmt)` |
| `b3` (response to other first messages with the same digest) | `ChainB3.ec` | `ga_b3` | `27 (qh1 + qsig + 2)^3 p_max(dview)` |
| `b1` (accepted check against an inconsistent token) | `ChainB1a.ec` | `ga_bbx`, `bbx_o2h` | `Pr[b1 and not Ept]` moved to eager commitments: `2 (qh0 + t qsig) sqrt(qsig pw) + qsig^2 pw` |
| | `ChainB1b.ec` | `bbx_col`, `bbx_b1col` | eager `Pr[b1 and not Ept] <= 27 (qh0 + (1 + t) qsig + 2)^3 p_max(dcmt)` |
| | `ChainB1c.ec` | `bbx_lef`, `lef_ept`, `pmem` | `Ept` implies the sampling flag `badE` of the instrumented lazy game; each sampling hits a logged point with probability at most (logged points of the token) `pw` |
| | `ChainB1d.ec` | `lef_fel`, `lef_badE`, `ept_bound`, `ga_b1` | `Pr[Ept] <= qsig (2 qsig - 1) pw` by the failure event lemma (counter `Cnt.cs < 2 qsig`, at most `Cnt.cs` logged points per token), and the closed bound on `Pr[b1]`, the sum of the three terms above |

Additional section hypotheses of these files: `reg_agg` (an aggregate commitment with one
fresh opening takes each value with probability at most `pw2`, second part of the regularity
lemma), `alpha_unit` (evaluation points are units) and `alpha_sep` (differences of distinct
evaluation points are units), and the premise `rounding_fact` of `gh_bound`.

### Main Theorem

`ChainMain.ec` instantiates every section above with one adversary and proves

```
lemma thimza_main &m :
  rounding_fact =>
  Pr[G0(A).main() @ &m : res]
  <= `|Pr[MPRFG(B1(A)).real() @ &m : res] - Pr[MPRFG(B1(A)).ideal() @ &m : res]|
     + `|Pr[HMLWE(B2(A)).main(true) @ &m : res] - Pr[HMLWE(B2(A)).main(false) @ &m : res]|
     + Pr[STM(B3(A)).main() @ &m : res]
     + eps_main.
```

for every adversary `A` that satisfies the section hypotheses `A_ll`, `A_bnd`, `e1_inj`,
`reg_open`, `reg_agg`, `alpha_unit` and `alpha_sep`. The three reductions are those of
Theorem main: `B1` against the multi-instance PRF, `B2` against HintMLWE and `B3` against
SelfTargetMSIS. The statistical loss `eps_main` is spelled out in the file as the sum of
eight terms, in this order: the digest collision of the simulation, the lazy commitments,
the extraction (`eps_ext`), the reprogramming of the challenge, the flag `bP`, the flag `b1`
(`eps_b1`), the flag `b2` and the flag `b3`. The flag `bC` has probability 0, and the hint
flag `bH` is covered by `bP` and `bC`.
