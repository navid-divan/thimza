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

## Modelling Conventions

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

Here, we have included `Params.ec` for the algebraic core $R_q = Z_q[X]/(X^{n}+1)$ as a proved commutative ring, $R_q^ell$ vectors/matrices, uniform distributions with losslessness, fullness, uniformity, finite sums, and cancellation lemmas `vsubK`/`vaddS`/`vcancelL`, `Types.ec` for abstract types (`msg`, `cmt`, `view`), Shamir points `alpha`, well formed committees, and seed distribution realized as a vector distribution, `Sharing.ec` for Shamir sharing over $R_q$, Lagrange coefficients via interpolation identities, reconstruction theorem, uniqueness across coefficient families, and perfect hiding of a single share, `Masking.ec` for antisymmetric pairwise masking, the zero sum theorem, partner count, and one-time-pad equivalences for uniform masked responses, `Assumptions.ec` for the public matrix, rounding/hash operators, and hardness assumptions (MLWE, Self-Target MSIS, Hint-MLWE) as EasyCrypt games, `PRFSecurity.ec` for pairwise masking as a keyed PRF, real/ideal PRF experiments, and proof that a fresh ideal query is uniform, `KeyGen.ec` for coefficient list distribution, losslessness/fullness, and share correctness under reconstruction, `Protocol.ec` for the three signing rounds, commitment predicate, honest-opening lemma, and view-only dependence of responses, `Combine.ec` for the combiner/hint, aggregation identity, and acceptance of honestly combined signatures under honest challenges, `Verify.ec` for single-signer vs. Thimza verifiers as separate modules with an `equiv` proof of behavioural equality, `Correctness.ec` for the correctness theorem as honest signatures verify within the correctness bound, `ViewPartition.ec` for the view-partition lemma as committee splits induce additive vector-sum splits, `Statelessness.ec` for view-only response dependence and a linear algebra attack recovering share/mask/nonce from two responses on one nonce, `Hierarchy.ec` for TS-UF-0/TS-UF-CA oracle interfaces and singleton-committee degeneracy at threshold one, `EUFCMA.ec` for the plain Fiat–Shamir signing procedure and proof that a singleton-committee threshold protocol equals it, `Security.ec` for the TS-UF-CA experiment, perfect indistinguishability of real/simulated signing oracles, and reduction of TS-UF-CA unforgeability to the core forgery game.

