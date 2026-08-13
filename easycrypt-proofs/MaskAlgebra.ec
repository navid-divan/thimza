require import AllCore Int List Distr.
require import Params Types BigOps Masking ViewPartition.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

(* The mask of a signer under two agreeing views is the same *)
lemma mask_view_congr (T : committee) (vw1 vw2 : view) (i : int) :
  vw1 = vw2 => mask T vw1 i = mask T vw2 i.
proof. by move=> ->. qed.

(* A signer outside the committee contributes the empty mask *)
lemma mask_nil (vw : view) (i : int) : mask [] vw i = zerov.
proof. by rewrite /mask vmap_nil. qed.

(* A one member committee produces no mask at all *)
lemma mask_singleton (vw : view) (i : int) : mask [i] vw i = zerov.
proof. by rewrite /mask vmap_cons vmap_nil term_diag; smt(RqVec.Vector.ZModule.addr0). qed.

(* The mask of a two member committee is one pseudorandom term *)
lemma mask_pair (vw : view) (i j : int) :
  i <> j => mask [i; j] vw i = term [i; j] vw i j.
proof.
move=> hij.
rewrite /mask !vmap_cons vmap_nil term_diag.
by smt(RqVec.Vector.ZModule.add0r RqVec.Vector.ZModule.addr0).
qed.

(* Two partners in a pair produce opposite masks *)
lemma mask_pair_anti (vw : view) (i j : int) :
  i <> j => mask [i; j] vw i + mask [j; i] vw j = zerov.
proof.
move=> hij.
rewrite (mask_pair vw i j hij) (mask_pair vw j i _) 1:/#.
rewrite /term.
have -> /= : !(i = j) by smt().
have -> /= : !(j = i) by smt().
case: (i < j) => hlt.
+ have -> /= : !(j < i) by smt().
  exact RqVec.Vector.ZModule.addrN.
have -> /= : j < i by smt().
exact RqVec.Vector.ZModule.addNr.
qed.

(* Adding a signer extends the mask by one pseudorandom term *)
lemma mask_cons (T : committee) (vw : view) (a i : int) :
  mask (a :: T) vw i = term (a :: T) vw i a + mask T vw i.
proof.
rewrite /mask vmap_cons.
congr; apply vmap_eq => j hj.
by rewrite /term.
qed.

(* The masking terms of a committee do not depend on the committee *)
lemma term_committee_free (T1 T2 : committee) (vw : view) (i j : int) :
  term T1 vw i j = term T2 vw i j.
proof. by rewrite /term. qed.

(* The total mask of a committee only reads its member list *)
lemma mask_committee_only (T1 T2 : committee) (vw : view) (i : int) :
  T1 = T2 => mask T1 vw i = mask T2 vw i.
proof. by move=> ->. qed.

(* The sum of masks over a class of the view partition *)
lemma mask_class_sum (T : committee) (vw : view) (cl : int -> int) (k : int) :
  vmap (mask T vw) (classOf T cl k) + vmap (mask T vw) (outClass T cl k)
  = zerov.
proof.
by rewrite (classOf_partition_sum T cl (mask T vw) k) mask_sum_zero.
qed.

(* Masking a family leaves its aggregate over a class unchanged only jointly *)
lemma mask_agg_classes (T : committee) (vw : view) (cl : int -> int)
                       (k : int) (g : int -> vec) :
  vmap (fun i => g i + mask T vw i) (classOf T cl k)
  + vmap (fun i => g i + mask T vw i) (outClass T cl k)
  = vmap g T.
proof.
rewrite (classOf_partition_sum T cl (fun i => g i + mask T vw i) k).
exact (mask_agg T vw g).
qed.

(* An unmatched class carries the mask of its own members only *)
lemma class_mask_residue (T : committee) (vw : view) (cl : int -> int)
                         (k : int) (g : int -> vec) :
  vmap (fun i => g i + mask T vw i) (classOf T cl k)
  = vmap g (classOf T cl k) + vmap (mask T vw) (classOf T cl k).
proof.
rewrite vmap_split; congr.
by apply vmap_eq.
qed.

(* Each signer masks against exactly the other committee members *)
lemma mask_partner_count (T : committee) (i : int) :
  wf_committee T => i \in T => size (partners T i) = tthr - 1.
proof. exact (partners_wf T i). qed.

(* The masking cost of a committee is linear in its size *)
lemma mask_total_count (T : committee) :
  wf_committee T =>
  forall i, i \in T => size (partners T i) = size T - 1.
proof. by move=> [hu hs] i hi; exact (partners_size T i hu hi). qed.
