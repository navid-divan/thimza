require import AllCore Int List Distr.
require import Params Types Sharing Masking.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

(* Committee members of a fixed class *)
op classOf (T : committee) (cl : int -> int) (k : int) : committee =
  filter (fun i => cl i = k) T.

(* Committee members outside a fixed class *)
op outClass (T : committee) (cl : int -> int) (k : int) : committee =
  filter (fun i => cl i <> k) T.

(* Every member recognizes its own class *)
lemma classOf_mem (T : committee) (cl : int -> int) (i : int) :
  i \in T => i \in classOf T cl (cl i).
proof. by move=> hi; rewrite mem_filter hi. qed.

(* Class membership and its complement exclude *)
lemma classOf_outClass_excl (T : committee) (cl : int -> int) (k i : int) :
  i \in classOf T cl k => i \in outClass T cl k => false.
proof.
rewrite /classOf /outClass !mem_filter => h1 h2.
smt().
qed.

(* Disjoint index families sum additively *)
lemma vmap_disjoint_union (T1 T2 : committee) (g : int -> vec) :
  vmap g (T1 ++ T2) = vmap g T1 + vmap g T2.
proof.
elim T1 => [| a T1 ih].
+ by rewrite cat0s vmap_nil RqVec.Vector.ZModule.add0r.
rewrite cat_cons !vmap_cons ih.
by rewrite (RqVec.Vector.ZModule.addrA (g a) (vmap g T1) (vmap g T2)).
qed.

(* Class filters split any vector sum *)
lemma classOf_partition_sum (T : committee) (cl : int -> int) (g : int -> vec) (k : int) :
  vmap g (classOf T cl k) + vmap g (outClass T cl k) = vmap g T.
proof.
rewrite /classOf /outClass.
elim T => [| a T ih] //=.
+ by rewrite vmap_nil RqVec.Vector.ZModule.add0r.
case: (cl a = k) => hca //=.
+ rewrite !vmap_cons -ih.
  by rewrite (RqVec.Vector.ZModule.addrA (g a) (vmap g (filter (fun i => cl i = k) T))
              (vmap g (filter (fun i => cl i <> k) T))).
rewrite !vmap_cons -ih.
have -> : g a + (vmap g (filter (fun i => cl i = k) T) + vmap g (filter (fun i => cl i <> k) T))
        = vmap g (filter (fun i => cl i = k) T) + (g a + vmap g (filter (fun i => cl i <> k) T)).
+ by rewrite (RqVec.Vector.ZModule.addrCA (g a)).
done.
qed.

(* A missing class carries no contribution *)
lemma classOf_empty (T : committee) (cl : int -> int) (k : int) :
  (forall i, i \in T => cl i <> k) => classOf T cl k = [].
proof.
move=> h; rewrite /classOf -size_eq0 size_filter.
apply (count_pred0_eq_in (fun i => cl i = k) T) => i hi.
by move: (h i hi) => /=.
qed.

(* Class masks recombine into the total *)
lemma mask_class_agg (T : committee) (vw : view) (cl : int -> int) (k : int) (g : int -> vec) :
  vmap (fun i => g i + mask T vw i) (classOf T cl k)
  = vmap g (classOf T cl k) + vmap (fun i => mask T vw i) (classOf T cl k).
proof. by rewrite -vmap_split. qed.
