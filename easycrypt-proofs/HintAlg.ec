require import AllCore Int List.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption Protocol.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

(* Row scaling distributes over addition *)
lemma rowZDl (c : rq) (x y : row) : rowZ c (x + y) = rowZ c x + rowZ c y.
proof. exact rowZD. qed.

(* Shared terms cancel in differences *)
lemma grp_cancel (a b d x : row) : a + b + (d + x) - (a + d) = b + x.
proof.
rewrite RqRow.Vector.ZModule.opprD.
smt(RqRow.Vector.ZModule.addrA RqRow.Vector.ZModule.addrC RqRow.Vector.ZModule.addNr
    RqRow.Vector.ZModule.add0r).
qed.

(* Hints recompute the hidden commitment *)
lemma hint_commit (s : vec) (e : row) (r : vec) (e' : row) (c : rq) :
  mulA mA (c ** s + r) + (rowZ c e + e') - rowZ c (mulA mA s + e) = mulA mA r + e'.
proof.
rewrite mulAD mulAZ rowZDl.
exact (grp_cancel (rowZ c (mulA mA s)) (mulA mA r) (rowZ c e) e').
qed.

(* Sums of three families split *)
lemma vmap_add3 (f g k : 'a -> vec) (L : 'a list) :
  vmap (fun x => f x + g x + k x) L = vmap f L + vmap g L + vmap k L.
proof.
elim: L => [| a L ih].
+ by rewrite !vmap_nil; smt(RqVec.Vector.ZModule.addr0).
rewrite !vmap_cons /= ih.
smt(RqVec.Vector.ZModule.addrA RqVec.Vector.ZModule.addrC).
qed.

(* Honest aggregates via the full key *)
lemma honest_aggregate (T : committee) (C : corrset) (vw : view) (c : rq)
                       (lam : int -> rq) (s : vec) (p : int -> vec) (r : int -> vec) :
  recons T lam =>
  vmap (fun h => (Rq.( * ) c (lam h)) ** shr s p h + r h + mask T vw h) (honest T C)
  = c ** s - vmap (fun j => (Rq.( * ) c (lam j)) ** shr s p j) (corrupted T C)
    + vmap r (honest T C) - vmap (mask T vw) (corrupted T C).
proof.
move=> hrec.
pose K := fun j => (Rq.( * ) c (lam j)) ** shr s p j.
have hK : vmap K (honest T C) + vmap K (corrupted T C) = c ** s.
+ rewrite honest_corrupted_split.
  have -> : vmap K T = vmap (fun j => c ** (lam j ** shr s p j)) T.
  - by apply vmap_eq => j _; rewrite /K vscaleA.
  by rewrite -scalev_vmap (shr_recons T lam s p hrec).
have hM : vmap (mask T vw) (honest T C) + vmap (mask T vw) (corrupted T C) = zerov.
+ by rewrite honest_corrupted_split mask_sum_zero.
have e1 := vmap_add3 K r (mask T vw) (honest T C).
have -> : vmap (fun h => (Rq.( * ) c (lam h)) ** shr s p h + r h + mask T vw h) (honest T C)
        = vmap (fun h => K h + r h + mask T vw h) (honest T C) by done.
rewrite e1.
have hK' : vmap K (honest T C) = c ** s - vmap K (corrupted T C).
+ rewrite -hK; smt(RqVec.Vector.ZModule.addrK).
have hM' : vmap (mask T vw) (honest T C) = - vmap (mask T vw) (corrupted T C).
+ smt(RqVec.Vector.ZModule.addrK RqVec.Vector.ZModule.add0r).
by rewrite hK' hM'.
qed.

(* The last response closes the sum *)
lemma last_response (agg prev zl : vec) : agg = prev + zl => zl = agg - prev.
proof.
move=> ->.
smt(RqVec.Vector.ZModule.addrC RqVec.Vector.ZModule.addKr).
qed.
