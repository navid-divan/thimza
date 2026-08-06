require import AllCore Int List Distr.
require import Params Types Sharing Masking Assumptions Protocol Combine Verify.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

(* Aggregated commitment from honest openings *)
op wHon (r : int -> vec) (T : committee) : vec = rndw (vmap r T).

(* Honest Fiat Shamir challenge *)
op cHon (t : vec) (mu : msg) (r : int -> vec) (T : committee) : rq =
  Hchal t (wHon r T) mu.

(* Combined response of an honest execution *)
op zHon (t : vec) (mu : msg) (T : committee) (lam : int -> rq)
        (s : vec) (p r : int -> vec) (vw : view) : vec =
  zcomb T (fun i => (Rq.( * ) (cHon t mu r T) (lam i)) ** shr s p i + r i + mask T vw i).

(* Combiner hint of an honest execution *)
op hHon (t : vec) (mu : msg) (T : committee) (lam : int -> rq)
        (s : vec) (p r : int -> vec) (vw : view) : vec =
  mkhint t (cHon t mu r T) (wHon r T) (zHon t mu T lam s p r vw).

(* The honestly produced signature *)
op sigHon (t : vec) (mu : msg) (T : committee) (lam : int -> rq)
          (s : vec) (p r : int -> vec) (vw : view) : sig =
  (cHon t mu r T, zHon t mu T lam s p r vw, hHon t mu T lam s p r vw).

(* Honest transcripts respect the correctness norm bound *)
op honestBound (t : vec) (mu : msg) (T : committee) (lam : int -> rq)
               (s : vec) (p r : int -> vec) (vw : view) : bool =
  inbnd (zHon t mu T lam s p r vw) (hHon t mu T lam s p r vw).

(* In bound honest signatures verify *)
lemma correctness (t : vec) (mu : msg) (T : committee) (lam : int -> rq)
                  (s : vec) (p r : int -> vec) (vw : view) :
  honestBound t mu T lam s p r vw =>
  vrfy t mu (sigHon t mu T lam s p r vw).
proof.
move=> hb; rewrite /sigHon.
apply (combine_verifies t mu (cHon t mu r T) (wHon r T) (zHon t mu T lam s p r vw)).
+ done.
by move: hb; rewrite /honestBound /hHon.
qed.

(* Honest response matches the aggregation identity *)
lemma zHon_agg (t : vec) (mu : msg) (T : committee) (lam : int -> rq)
               (s : vec) (p r : int -> vec) (vw : view) :
  recons T lam =>
  zHon t mu T lam s p r vw = (cHon t mu r T) ** s + vmap r T.
proof.
move=> hrec.
by apply (agg_identity T lam (cHon t mu r T) s p r (fun T0 vw0 i => mask T0 vw0 i) vw hrec).
qed.
