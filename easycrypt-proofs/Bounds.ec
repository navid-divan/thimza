require import AllCore Int List Distr Real.
require import Params Types BigOps Assumptions.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

(* The verification bound of the signature scheme *)
op bnd : int.

(* A norm on the response space of the scheme *)
op nrm : vec -> int.

(* The defining properties of a norm on the response space *)
pred isNorm (f : vec -> int) =
  (forall v, 0 <= f v)
  /\ f zerov = 0
  /\ (forall u v, f (u + v) <= f u + f v)
  /\ (forall v, f (- v) = f v).

(* A norm never takes a negative value *)
lemma norm_ge0 (f : vec -> int) (v : vec) : isNorm f => 0 <= f v.
proof. by rewrite /isNorm => -[h _]; exact h. qed.

(* A norm sends the zero vector to zero *)
lemma norm_zero (f : vec -> int) : isNorm f => f zerov = 0.
proof. by rewrite /isNorm => -[_ [h _]]; exact h. qed.

(* A norm obeys the triangle inequality *)
lemma norm_tri (f : vec -> int) (u v : vec) :
  isNorm f => f (u + v) <= f u + f v.
proof. by rewrite /isNorm => -[_ [_ [h _]]]; exact h. qed.

(* A norm is invariant under negation *)
lemma norm_neg (f : vec -> int) (v : vec) : isNorm f => f (- v) = f v.
proof. by rewrite /isNorm => -[_ [_ [_ h]]]; exact h. qed.

(* The norm of a difference is bounded by the sum of the norms *)
lemma norm_sub (f : vec -> int) (u v : vec) :
  isNorm f => f (u - v) <= f u + f v.
proof.
move=> hn; have := norm_tri f u (- v) hn.
by rewrite (norm_neg f v hn).
qed.

(* A finite sum has norm at most the sum of the norms *)
lemma norm_vmap (f : vec -> int) (g : 'a -> vec) (L : 'a list) :
  isNorm f =>
  f (vmap g L) <= foldr (fun x acc => f (g x) + acc) 0 L.
proof.
move=> hn; elim L => [| a L ih] /=.
+ by rewrite vmap_nil (norm_zero f hn).
rewrite vmap_cons.
have := norm_tri f (g a) (vmap g L) hn.
by smt().
qed.

(* An honest transcript stays inside the verification bound *)
op inBound (f : vec -> int) (z h : vec) : bool = f z + f h <= bnd.

(* Being inside the bound is preserved by a tighter transcript *)
lemma inBound_mono (f : vec -> int) (z h z' h' : vec) :
  f z' <= f z => f h' <= f h => inBound f z h => inBound f z' h'.
proof. by rewrite /inBound; smt(). qed.

(* A transcript at the origin is always inside a nonnegative bound *)
lemma inBound_zero (f : vec -> int) :
  isNorm f => 0 <= bnd => inBound f zerov zerov.
proof. by move=> hn hb; rewrite /inBound !(norm_zero f hn). qed.

(* The aggregated response norm grows at most additively *)
lemma norm_agg (f : vec -> int) (T : committee) (r : int -> vec)
               (c : rq) (s : vec) :
  isNorm f =>
  f (c ** s + vmap r T) <= f (c ** s) + f (vmap r T).
proof. by move=> hn; exact (norm_tri f (c ** s) (vmap r T) hn). qed.

(* Two transcripts inside the bound have bounded difference *)
lemma inBound_diff (f : vec -> int) (z1 h1 z2 h2 : vec) :
  isNorm f => inBound f z1 h1 => inBound f z2 h2 =>
  f (z1 - z2) <= 2 * bnd.
proof.
move=> hn; rewrite /inBound => h1b h2b.
have := norm_sub f z1 z2 hn.
by smt(norm_ge0).
qed.

(* The scheme bound predicate refines any concrete norm choice *)
lemma inBound_refines (f : vec -> int) (z h : vec) :
  isNorm f => inBound f z h => f z <= bnd.
proof. by move=> hn; rewrite /inBound; smt(norm_ge0). qed.
