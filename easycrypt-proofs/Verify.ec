require import AllCore Int List Distr.
require import Params Types Sharing Masking Assumptions Protocol Combine.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

(* The unmodified single signer Raccoon verifier *)
module RaccooonVerify = {
  proc verify(t : vec, mu : msg, sg : sig) : bool = {
    var c : rq;
    var z, h, w' : vec;
    var b1, b2 : bool;
    (c, z, h) <- sg;
    w' <- rndw (mA *^ z - c ** liftt t) + h;
    b1 <- (c = Hchal t w' mu);
    b2 <- inbnd z h;
    return b1 /\ b2;
  }
}.

(* The Thimza verifier presented to callers *)
module ThimzaVerify = {
  proc verify(t : vec, mu : msg, sg : sig) : bool = {
    return vrfy t mu sg;
  }
}.

(* Functional interchangeability of the verifier *)
equiv interchangeable :
  ThimzaVerify.verify ~ RaccooonVerify.verify : ={t, mu, sg} ==> ={res}.
proof.
proc.
inline ThimzaVerify.verify.
wp; skip => &1 &2 [<- [<- <-]] /=.
rewrite /vrfy /=.
by smt().
qed.

(* Accepted combined signatures verify with base *)
lemma combine_interchangeable (t0 : vec) (mu0 : msg) (sg0 : sig) :
  hoare[RaccooonVerify.verify :
        t = t0 /\ mu = mu0 /\ sg = sg0 /\ vrfy t0 mu0 sg0 ==> res].
proof.
proc.
wp; skip => &hr [-> [-> [-> hv]]] /=.
move: hv; rewrite /vrfy /=.
by smt().
qed.
