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

## Modelling Mechanism

$R_q$ is the quotient ring obtained from the EasyCrypt library theory
`PolyReduce.PolyReduceZp`, so its ring laws are proved rather than assumed.
Vectors of dimension `ell` come from the library theory `Matrix`, which
supplies the module laws, the matrix–vector product, and the uniform product
distribution with its standard properties. The masking seeds are in the same
vector space as the ring vectors, so their distribution is the already proven
vector distribution rather than a separately axiomatised one.

We modeled pairwise masking function as a keyed pseudorandom function in
`PRFSecurity.ec`, with the real/ideal experiments standard in the EasyCrypt; the games in `Assumptions.ec` for MLWE, Self-Target MSIS and
Hint-MLWE are similarly stated as adversary experiments, which is the standard
way an external hardness assumption is recorded in a machine-checked proof.


## Proof Content

Here, we have included `Params.ec` for the algebraic core $R_q = Z_q[X]/(X^{\phi}+1)$ as a proved commutative ring, the module $R_q^{\ell}$, matrices, uniform distributions, finite sums, and cancellation lemmas, `Types.ec` for the abstract types of the scheme, evaluation points, well formed committees, and the seed distribution realized as the vector distribution, `BigOps.ec` for the finite operator library of ring products, concatenation, permutation invariance, exchange of double sums, and filtered sums, `PolyList.ec` for polynomials as coefficient lists, evaluation, synthetic division, the factor theorem, and the roots lemma, `Lagrange.ec` for the Lagrange basis, interpolation identities, and reconstruction coefficients as a construction, `Sharing.ec` for Shamir sharing over $R_q$, the reconstruction theorem, and hiding of a single share, `ShamirLagrange.ec` for the connection discharging the reconstruction hypothesis for all well formed committees, `Masking.ec` for antisymmetric masks, and the zero sum theorem, `Assumptions.ec` for MLWE, SelfTarget MSIS, and HintMLWE as adversary experiments, `Bounds.ec` for the norm and verification bound, with norm properties carried as an explicit `isNorm` hypothesis, `ROM.ec` for the challenge random oracle, freshness, determinism on repeats, and programmability, `PRFSecurity.ec` for the masking function as a keyed pseudorandom function with real and ideal experiments, `KeyGen.ec` for key generation, the coefficient distribution, and correctness of the resulting shares, `Protocol.ec` for the three signing rounds as procedures, the commitment check, and the honest opening lemma, `Combine.ec` for the combiner, the hint, and the aggregation identity, `Verify.ec` for the two verifiers as separate modules with a proof of behavioural equality, `Interchange.ec` for interchangeability in both directions, with acceptance and rejection transfer, `Correctness.ec` for the theorem that an honest signature verifies inside the bound, `ViewPartition.ec` for the view-partition lemma and the class decomposition of a committee, `MaskAlgebra.ec` for the mask algebra of pairs, cons, class residues, and linear masking cost, `Simulator.ec` for the joint simulator over a signer list, with the closing share and aggregate agreement, `Corruption.ec` for static corruption, the honest/corrupted split, and the bounded corruption oracle, `Statelessness.ec` for the share, mask, and nonce recovery attacks behind the statelessness result, `Hierarchy.ec` for the TS-UF-0 and TS-UF-CA oracle interfaces and the singleton committee, `EUFCMA.ec` for the proof that the singleton protocol computes exactly the plain Fiat–Shamir signature, `GameHops.ec` for the hop sequence with explicit probability equalities and the advantage bound, and `Security.ec` for the unforgeability experiment, the oracle simulation, and the reduction.

