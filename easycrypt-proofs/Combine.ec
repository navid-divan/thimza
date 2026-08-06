require import AllCore Int List Distr.
require import Params Types Sharing Masking Assumptions Protocol.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

type sig = rq * vec * vec.

(* Round three responses combined into one signature *)
op zcomb (T : committee) (zs : int -> vec) : vec = vmap zs T.

(* Combiner hint operator *)
op mkhint (t : vec) (c : rq) (w z : vec) : vec = w - rndw (mA *^ z - c ** liftt t).

module Combine = {
  proc run(t : vec, w : vec, c : rq, T : committee, zs : int -> vec) : sig = {
    var z, h : vec;
    z <- zcomb T zs;
    h <- mkhint t c w z;
    return (c, z, h);
  }
}.

(* The single signer base verifier *)
op vrfy (t : vec) (mu : msg) (sg : sig) : bool =
  let (c, z, h) = sg in
  c = Hchal t (rndw (mA *^ z - c ** liftt t) + h) mu /\ inbnd z h.

(* Combined response equals one aggregated share *)
lemma agg_identity (T : committee) (lam : int -> rq) (c : rq) (s : vec)
                   (p r : int -> vec) (F : committee -> view -> int -> vec) (vw : view) :
  recons T lam =>
  (forall i, F T vw i = mask T vw i) =>
  zcomb T (fun i => (Rq.( * ) c (lam i)) ** shr s p i + r i + F T vw i) = c ** s + vmap r T.
proof.
move=> hrec hF; rewrite /zcomb.
have -> : vmap (fun i => (Rq.( * ) c (lam i)) ** shr s p i + r i + F T vw i) T
        = vmap (fun i => (Rq.( * ) c (lam i)) ** shr s p i + r i) T
        + vmap (fun i => F T vw i) T.
+ by rewrite -vmap_split.
have -> : vmap (fun i => F T vw i) T = vmap (mask T vw) T.
+ by apply vmap_eq => i _; exact (hF i).
rewrite mask_sum_zero RqVec.Vector.ZModule.addr0.
have -> : vmap (fun i => (Rq.( * ) c (lam i)) ** shr s p i + r i) T
        = vmap (fun i => (Rq.( * ) c (lam i)) ** shr s p i) T + vmap r T.
+ by rewrite -vmap_split.
congr.
have -> : vmap (fun i => (Rq.( * ) c (lam i)) ** shr s p i) T
        = vmap (fun i => c ** (lam i ** shr s p i)) T.
+ by apply vmap_eq => i _ /=; rewrite vscaleA.
by rewrite -scalev_vmap (shr_recons T lam s p hrec).
qed.

(* Combined public image matches aggregated shares *)
lemma agg_image (T : committee) (lam : int -> rq) (c : rq) (s : vec)
                (p r : int -> vec) (F : committee -> view -> int -> vec) (vw : view) :
  recons T lam =>
  (forall i, F T vw i = mask T vw i) =>
  mA *^ (zcomb T (fun i => (Rq.( * ) c (lam i)) ** shr s p i + r i + F T vw i))
  = c ** (mA *^ s) + vmap (fun i => mA *^ r i) T.
proof.
move=> hrec hF.
rewrite (agg_identity T lam c s p r F vw hrec hF).
by rewrite RqVec.Matrix.mulmxvDr mulmxvZ mulmxv_vmap.
qed.

(* Combiner hint recovers aggregated commitment *)
lemma hint_correct (t : vec) (c : rq) (w z : vec) :
  rndw (mA *^ z - c ** liftt t) + mkhint t c w z = w.
proof. by rewrite /mkhint vaddS. qed.

(* Honest challenges make combined signatures accepted *)
lemma combine_verifies (t : vec) (mu : msg) (c : rq) (w z : vec) :
  c = Hchal t w mu => inbnd z (mkhint t c w z) => vrfy t mu (c, z, mkhint t c w z).
proof. by move=> hc hb; rewrite /vrfy /= hint_correct -hc hb. qed.
