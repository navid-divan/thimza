require import AllCore Int List Distr.
require import Params Types BigOps Masking ViewPartition.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

(* Agreeing views give equal masks *)
lemma mask_view_congr (T : committee) (vw1 vw2 : view) (i : int) :
  vw1 = vw2 => mask T vw1 i = mask T vw2 i.
proof. by move=> ->. qed.

(* Empty committees give empty masks *)
lemma mask_nil (vw : view) (i : int) : mask [] vw i = zerov.
proof. by rewrite /mask vmap_nil. qed.

(* Singleton committees produce no mask *)
lemma mask_singleton (vw : view) (i : int) : mask [i] vw i = zerov.
proof. by rewrite /mask vmap_cons vmap_nil term_diag; smt(RqVec.Vector.ZModule.addr0). qed.

(* Pair committees use one term *)
lemma mask_pair (vw : view) (i j : int) :
  i <> j => mask [i; j] vw i = term [i; j] vw i j.
proof.
move=> hij.
rewrite /mask !vmap_cons vmap_nil term_diag.
by smt(RqVec.Vector.ZModule.add0r RqVec.Vector.ZModule.addr0).
qed.

(* Pair partners produce opposite masks *)
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

(* New signers add one mask term *)
lemma mask_cons (T : committee) (vw : view) (a i : int) :
  mask (a :: T) vw i = term (a :: T) vw i a + mask T vw i.
proof.
rewrite /mask vmap_cons.
congr; apply vmap_eq => j hj.
by rewrite /term.
qed.

(* Mask terms ignore the committee *)
lemma term_committee_free (T1 T2 : committee) (vw : view) (i j : int) :
  term T1 vw i j = term T2 vw i j.
proof. by rewrite /term. qed.

(* Masks only read the member list *)
lemma mask_committee_only (T1 T2 : committee) (vw : view) (i : int) :
  T1 = T2 => mask T1 vw i = mask T2 vw i.
proof. by move=> ->. qed.

(* Class mask sums *)
lemma mask_class_sum (T : committee) (vw : view) (cl : int -> int) (k : int) :
  vmap (mask T vw) (classOf T cl k) + vmap (mask T vw) (outClass T cl k)
  = zerov.
proof.
by rewrite (classOf_partition_sum T cl (mask T vw) k) mask_sum_zero.
qed.

(* Class aggregates of masked families *)
lemma mask_agg_classes (T : committee) (vw : view) (cl : int -> int)
                       (k : int) (g : int -> vec) :
  vmap (fun i => g i + mask T vw i) (classOf T cl k)
  + vmap (fun i => g i + mask T vw i) (outClass T cl k)
  = vmap g T.
proof.
rewrite (classOf_partition_sum T cl (fun i => g i + mask T vw i) k).
exact (mask_agg T vw g).
qed.

(* Unmatched classes keep own masks *)
lemma class_mask_residue (T : committee) (vw : view) (cl : int -> int)
                         (k : int) (g : int -> vec) :
  vmap (fun i => g i + mask T vw i) (classOf T cl k)
  = vmap g (classOf T cl k) + vmap (mask T vw) (classOf T cl k).
proof.
rewrite vmap_split; congr.
by apply vmap_eq.
qed.

(* Signers mask against all partners *)
lemma mask_partner_count (T : committee) (i : int) :
  wf_committee T => i \in T => size (partners T i) = tthr - 1.
proof. exact (partners_wf T i). qed.

(* Masking cost is linear *)
lemma mask_total_count (T : committee) :
  wf_committee T =>
  forall i, i \in T => size (partners T i) = size T - 1.
proof. by move=> [hu hs] i hi; exact (partners_size T i hu hi). qed.
