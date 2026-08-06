require import AllCore Int List Distr.
require import Params Types.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

(* Public matrix of the deployment *)
op mA : mx.

(* Bound predicate defining an accepting signature norm *)
op inbnd : vec -> vec -> bool.

(* Commitment truncation rounding operator *)
op rndc : vec -> vec.

(* Aggregate truncation rounding operator *)
op rndw : vec -> vec.

(* Public key rounding operator *)
op rndt : vec -> vec.

(* Public key lift operator *)
op liftt : vec -> vec.

(* Commitment hash function *)
op Hcmt : vec -> msg -> int -> vec -> cmt.

(* Transcript view hash function *)
op Hview : vec -> msg -> committee -> cmt list -> vec list -> view.

(* Fiat Shamir challenge hash function *)
op Hchal : vec -> vec -> msg -> rq.

module type MLWEAdv = {
  proc guess(mA : mx, t : vec) : bool
}.

module MLWEReal (A : MLWEAdv) = {
  proc main() : bool = {
    var s, e, t : vec;
    var b : bool;
    s <$ dvec;
    e <$ dvec;
    t <- mA *^ s + e;
    b <@ A.guess(mA, t);
    return b;
  }
}.

module MLWEIdeal (A : MLWEAdv) = {
  proc main() : bool = {
    var t : vec;
    var b : bool;
    t <$ dvec;
    b <@ A.guess(mA, t);
    return b;
  }
}.

module type STMSISAdv = {
  proc forge(mA : mx, t : vec) : msg * rq * vec
}.

op stmsisWin (t z : vec) (c : rq) (mu : msg) : bool =
  c = Hchal t (rndw (mA *^ z - c ** liftt t)) mu /\ inbnd z zerov.

module STMSIS (A : STMSISAdv) = {
  proc main() : bool = {
    var s, e, t : vec;
    var mu : msg;
    var c : rq;
    var z : vec;
    s <$ dvec;
    e <$ dvec;
    t <- mA *^ s + e;
    (mu, c, z) <@ A.forge(mA, t);
    return stmsisWin t z c mu;
  }
}.

module type HintMLWEAdv = {
  proc guess(mA : mx, t : vec, hv : vec) : bool
}.

module HintMLWEReal (A : HintMLWEAdv) = {
  proc main() : bool = {
    var s, e, r, hv, t : vec;
    var b : bool;
    s <$ dvec;
    e <$ dvec;
    r <$ dvec;
    t <- mA *^ s + e;
    hv <- r - rndw (mA *^ r);
    b <@ A.guess(mA, t, hv);
    return b;
  }
}.

module HintMLWEIdeal (A : HintMLWEAdv) = {
  proc main() : bool = {
    var t, hv : vec;
    var b : bool;
    t <$ dvec;
    hv <$ dvec;
    b <@ A.guess(mA, t, hv);
    return b;
  }
}.
