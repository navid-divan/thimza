require import AllCore Int List Distr.
require import Params Types Masking.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

(* A fixed signer's response is functional *)
lemma respond_functional (lam : int -> rq) (si r : vec) (T : committee) (i : int) :
  exists (g : view -> rq -> vec),
    forall (vw : view) (c : rq),
      (Rq.( * ) c (lam i)) ** si + r + mask T vw i = g vw c.
proof.
by exists (fun vw c => (Rq.( * ) c (lam i)) ** si + r + mask T vw i).
qed.

(* Repeated challenges expose the linear share *)
lemma share_recovery (c c' l : rq) (si w z z' : vec) :
  z  = w + (Rq.( * ) c  l) ** si =>
  z' = w + (Rq.( * ) c' l) ** si =>
  Rq.ComRingDflInv.unit (Rq.( * ) (Rq.( + ) c (Rq.([-]) c')) l) =>
  si = (Rq.ComRingDflInv.invr (Rq.( * ) (Rq.( + ) c (Rq.([-]) c')) l)) ** (z - z').
proof.
move=> -> -> hu.
rewrite (vcancelL ((Rq.( * ) c l) ** si) ((Rq.( * ) c' l) ** si) w).
have e2 : (Rq.( * ) c l) ** si - (Rq.( * ) c' l) ** si
        = (Rq.( * ) (Rq.( + ) c (Rq.([-]) c')) l) ** si.
+ rewrite -vscaleN -vscaleDl; congr.
  by rewrite Rq.ComRingDflInv.mulrDl Rq.ComRingDflInv.mulNr.
by rewrite e2 (vscaleKV _ _ hu).
qed.

(* Answering twice unmasked loses the share *)
lemma stateless_break (c c' l : rq) (si r z z' : vec) :
  c <> c' =>
  Rq.ComRingDflInv.unit (Rq.( * ) (Rq.( + ) c (Rq.([-]) c')) l) =>
  z  = r + (Rq.( * ) c  l) ** si =>
  z' = r + (Rq.( * ) c' l) ** si =>
  si = (Rq.ComRingDflInv.invr (Rq.( * ) (Rq.( + ) c (Rq.([-]) c')) l)) ** (z - z').
proof. by move=> hne hu hz hz'; apply (share_recovery c c' l si r). qed.

(* A known mask still exposes shares *)
lemma masked_break (c c' l : rq) (si w z z' : vec) :
  z  = w + (Rq.( * ) c  l) ** si =>
  z' = w + (Rq.( * ) c' l) ** si =>
  Rq.ComRingDflInv.unit (Rq.( * ) (Rq.( + ) c (Rq.([-]) c')) l) =>
  si = (Rq.ComRingDflInv.invr (Rq.( * ) (Rq.( + ) c (Rq.([-]) c')) l)) ** (z - z').
proof. exact (share_recovery c c' l si w). qed.

(* The mask is recoverable from responses *)
lemma mask_recovery (c l : rq) (si ri m z : vec) :
  z = (Rq.( * ) c l) ** si + ri + m =>
  m = z - ((Rq.( * ) c l) ** si + ri).
proof. move=> ->; by rewrite (vsubK ((Rq.( * ) c l) ** si + ri) m). qed.

(* Two responses determine the round nonce *)
lemma nonce_recovery (c l : rq) (si ri z m : vec) :
  z = (Rq.( * ) c l) ** si + m + ri =>
  ri = z - ((Rq.( * ) c l) ** si + m).
proof. move=> ->; by rewrite (vsubK ((Rq.( * ) c l) ** si + m) ri). qed.
