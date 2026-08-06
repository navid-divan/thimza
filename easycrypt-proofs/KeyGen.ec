require import AllCore Int List Distr DList.
require import Params Types Sharing Assumptions.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

(* Sharing polynomial tail coefficient distribution *)
op dcoeffs : vec list distr = dlist dvec (tthr - 1).

(* Coefficient list drawing is lossless *)
lemma dcoeffs_ll : is_lossless dcoeffs.
proof. by rewrite /dcoeffs; apply dlist_ll; exact dvec_ll. qed.

(* Coefficient distribution is full *)
lemma dcoeffs_fu (xs : vec list) :
  size xs = tthr - 1 => xs \in dcoeffs.
proof.
move=> hsz; rewrite /dcoeffs -hsz; apply dlist_fu => x hx.
by apply dvec_fu.
qed.

(* Sharing polynomial tail from coefficients *)
op polyOf (xs : vec list) (u : int) : vec = nth zerov xs (u - 1).

module KeyGen = {
  proc gen() : vec * vec * vec list = {
    var s, e, t : vec;
    var coeffs : vec list;
    s <$ dvec;
    e <$ dvec;
    coeffs <$ dcoeffs;
    t <- rndt (mA *^ s + e);
    return (s, t, coeffs);
  }

  proc share(s : vec, coeffs : vec list, i : int) : vec = {
    return shr s (polyOf coeffs) i;
  }
}.

module KeyGenIdealKey = {
  proc gen() : vec * vec * vec list = {
    var s, e, t : vec;
    var coeffs : vec list;
    t <$ dvec;
    s <$ dvec;
    e <$ dvec;
    coeffs <$ dcoeffs;
    return (s, t, coeffs);
  }
}.

(* Share reconstruction recovers the master secret *)
lemma keygen_share_recons (T : committee) (lam : int -> rq) (s0 : vec) (coeffs : vec list) :
  recons T lam => vmap (fun i => lam i ** shr s0 (polyOf coeffs) i) T = s0.
proof. exact (shr_recons T lam s0 (polyOf coeffs)). qed.

(* Every committee member has a share *)
lemma keygen_share_total (s0 : vec) (coeffs : vec list) (i : int) :
  exists (si : vec), si = shr s0 (polyOf coeffs) i.
proof. by exists (shr s0 (polyOf coeffs) i). qed.

(* Threshold one hands out the secret *)
lemma keygen_share_trivial (s0 : vec) (coeffs : vec list) (i : int) :
  tthr = 1 => shr s0 (polyOf coeffs) i = s0.
proof. exact (shr_share0 s0 (polyOf coeffs) i). qed.

