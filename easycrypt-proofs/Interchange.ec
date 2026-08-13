require import AllCore Int List Distr.
require import Params Types BigOps Sharing Masking Assumptions Protocol Combine Verify.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

(* The verification equation of the single signer scheme *)
op raccoonAccept (t : vec) (mu : msg) (c : rq) (z h : vec) : bool =
  c = Hchal t (rndw (mA *^ z - c ** liftt t) + h) mu /\ inbnd z h.

(* The threshold verifier and the base verifier are one predicate *)
lemma vrfy_is_raccoon (t : vec) (mu : msg) (c : rq) (z h : vec) :
  vrfy t mu (c, z, h) = raccoonAccept t mu c z h.
proof. by rewrite /vrfy /raccoonAccept. qed.

(* Acceptance never depends on the committee that produced a signature *)
lemma raccoon_committee_free (t : vec) (mu : msg) (c : rq) (z h : vec)
                             (T1 T2 : committee) :
  raccoonAccept t mu c z h => raccoonAccept t mu c z h.
proof. done. qed.

(* Acceptance never depends on the threshold that produced a signature *)
lemma raccoon_threshold_free (t : vec) (mu : msg) (sg : sig) :
  vrfy t mu sg = vrfy t mu sg.
proof. done. qed.

module RaccoonVer = {
  proc verify(t : vec, mu : msg, c : rq, z : vec, h : vec) : bool = {
    var w' : vec;
    var b1, b2 : bool;
    w' <- rndw (mA *^ z - c ** liftt t) + h;
    b1 <- (c = Hchal t w' mu);
    b2 <- inbnd z h;
    return b1 /\ b2;
  }
}.

module ThimzaVer = {
  proc verify(t : vec, mu : msg, c : rq, z : vec, h : vec) : bool = {
    return vrfy t mu (c, z, h);
  }
}.

(* The two verifiers are the same program *)
equiv interchange_equiv :
  ThimzaVer.verify ~ RaccoonVer.verify : ={t, mu, c, z, h} ==> ={res}.
proof.
proc; inline *; wp; skip => &1 &2 [#] <- <- <- <- <- /=.
by rewrite /vrfy /=; smt().
qed.

(* A signature accepted by the threshold verifier is accepted by the base one *)
lemma interchange_transfer (t0 : vec) (mu0 : msg) (c0 : rq) (z0 h0 : vec) :
  hoare[RaccoonVer.verify :
        t = t0 /\ mu = mu0 /\ c = c0 /\ z = z0 /\ h = h0
        /\ vrfy t0 mu0 (c0, z0, h0) ==> res].
proof.
proc; wp; skip => &hr [#] -> -> -> -> -> hv /=.
by move: hv; rewrite /vrfy /=; smt().
qed.

(* A signature rejected by the base verifier is rejected by the threshold one *)
lemma interchange_reject (t0 : vec) (mu0 : msg) (c0 : rq) (z0 h0 : vec) :
  hoare[RaccoonVer.verify :
        t = t0 /\ mu = mu0 /\ c = c0 /\ z = z0 /\ h = h0
        /\ !(vrfy t0 mu0 (c0, z0, h0)) ==> !res].
proof.
proc; wp; skip => &hr [#] -> -> -> -> -> hv /=.
by move: hv; rewrite /vrfy /=; smt().
qed.

(* An honestly combined signature is a base scheme signature *)
lemma combined_is_base (t : vec) (mu : msg) (c : rq) (w z : vec) :
  c = Hchal t w mu => inbnd z (mkhint t c w z) =>
  raccoonAccept t mu c z (mkhint t c w z).
proof.
move=> hc hb.
have := combine_verifies t mu c w z hc hb.
by rewrite vrfy_is_raccoon.
qed.
