require import AllCore Int List Distr.
require import Params Types Sharing Masking Assumptions KeyGen.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

(* Per session signer state *)
type sstate = vec * vec.

(* Round one commitment rounding operator *)
op rndc_of (r er : vec) : vec = rndc (mA *^ r + er).

module Round1 = {
  proc run(mA0 : mx) : vec * vec * vec = {
    var r, er, w : vec;
    r  <$ dvec;
    er <$ dvec;
    w  <- mA0 *^ r + er;
    return (r, er, w);
  }
}.

(* Commitment value of a signer *)
op mkcmt (t : vec) (mu : msg) (i : int) (w : vec) : cmt = Hcmt t mu i (rndc w).

module Round2 = {
  proc reveal(t : vec, mu : msg, i : int, w : vec) : cmt * vec = {
    return (mkcmt t mu i w, rndc w);
  }
}.

(* Whether all openings are consistent *)
op cmts_ok (t : vec) (mu : msg) (T : committee) (cs : cmt list) (ws : vec list) : bool =
  all (fun p => let (i, cw) = p in fst cw = mkcmt t mu i (snd cw))
      (zip T (zip cs ws)).

(* Aggregated challenge derived from the opened commitments *)
op chalOf (t : vec) (mu : msg) (T : committee) (cs : cmt list) (ws : vec list) : rq =
  let vw = Hview t mu T cs ws in
  let wagg = rndw (vmap (fun p => let (i, cw) = p in cw) (zip T ws)) in
  Hchal t wagg mu.

module Round3 = {
  proc respond(t : vec, mu : msg, T : committee, lam : int -> rq,
               si : vec, i : int, r er : vec,
               cs : cmt list, ws : vec list) : vec option = {
    var vw : view;
    var c : rq;
    var z : vec;
    var ok : bool;
    var outp : vec option;
    ok <- cmts_ok t mu T cs ws;
    if (ok) {
      vw <- Hview t mu T cs ws;
      c  <- chalOf t mu T cs ws;
      z  <- (Rq.( * ) c (lam i)) ** si + r + mask T vw i;
      outp <- Some z;
    } else {
      outp <- None;
    }
    return outp;
  }
}.

(* Honest openings satisfy the commitment check *)
lemma cmts_ok_honest (t : vec) (mu : msg) (T : committee) (ws : int -> vec) :
  cmts_ok t mu T (map (fun i => mkcmt t mu i (ws i)) T) (map ws T).
proof.
by rewrite /cmts_ok; elim T => [| a T ih] //=.
qed.

(* A fixed view determines the response *)
lemma respond_deterministic (t : vec) (mu : msg) (T : committee) (lam : int -> rq)
    (si r er : vec) (i : int) (cs : cmt list) (ws1 ws2 : vec list) :
  cmts_ok t mu T cs ws1 => cmts_ok t mu T cs ws2 =>
  Hview t mu T cs ws1 = Hview t mu T cs ws2 =>
  chalOf t mu T cs ws1 = chalOf t mu T cs ws2 =>
  (Rq.( * ) (chalOf t mu T cs ws1) (lam i)) ** si + r + mask T (Hview t mu T cs ws1) i
  = (Rq.( * ) (chalOf t mu T cs ws2) (lam i)) ** si + r + mask T (Hview t mu T cs ws2) i.
proof. by move=> _ _ hv hc; rewrite hv hc. qed.
