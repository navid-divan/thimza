require import AllCore Int List Distr.
require import Params Types BigOps PolyList Lagrange Sharing.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

(* The evaluation points attached to a committee *)
op nodesOf (T : committee) : rq list = map alpha T.

(* Committees whose evaluation points are distinct and separated *)
pred wf_nodes (T : committee) =
  sep (nodesOf T) /\ uniq (nodesOf T) /\ size (nodesOf T) = tthr.

(* The reconstruction coefficient attached to a signer *)
op lam_of (T : committee) (i : int) : rq = lagcoef (nodesOf T) (alpha i).

(* A well formed committee has as many nodes as its threshold *)
lemma size_nodesOf (T : committee) : size (nodesOf T) = size T.
proof. by rewrite /nodesOf size_map. qed.

(* Summing over a committee equals summing over its nodes *)
lemma rmap_nodesOf (T : committee) (g : rq -> rq) :
  rmap (fun i => g (alpha i)) T = rmap g (nodesOf T).
proof.
rewrite /nodesOf; elim T => [| a T ih] /=; first by rewrite !rmap_nil.
by rewrite !rmap_cons ih.
qed.

(* The constructed coefficients satisfy the reconstruction predicate *)
lemma lam_of_recons (T : committee) :
  wf_nodes T => 0 < tthr => recons T (lam_of T).
proof.
move=> [hsep [huniq hsz]] ht; split.
+ rewrite /lam_of (rmap_nodesOf T (fun a => lagcoef (nodesOf T) a)).
  by apply lagcoef_sum_one => //; smt().
move=> u [hu1 hu2].
rewrite /lam_of /ipow.
have -> : rmap (fun i => Rq.( * ) (lagcoef (nodesOf T) (alpha i))
                                 (Rq.ComRingDflInv.exp (alpha i) u)) T
        = rmap (fun a => Rq.( * ) (lagcoef (nodesOf T) a)
                                  (Rq.ComRingDflInv.exp a u)) (nodesOf T).
+ by apply (rmap_nodesOf T (fun a => Rq.( * ) (lagcoef (nodesOf T) a)
                                              (Rq.ComRingDflInv.exp a u))).
by apply lagcoef_idu => //; smt().
qed.

(* Reconstruction holds for the constructed coefficients *)
lemma shr_recons_constructed (T : committee) (s : vec) (p : int -> vec) :
  wf_nodes T => 0 < tthr =>
  vmap (fun i => lam_of T i ** shr s p i) T = s.
proof.
move=> hwf ht.
by apply (shr_recons T (lam_of T) s p (lam_of_recons T hwf ht)).
qed.

(* Every well formed committee admits reconstruction coefficients *)
lemma recons_exists (T : committee) :
  wf_nodes T => 0 < tthr => exists (lam : int -> rq), recons T lam.
proof. by move=> hwf ht; exists (lam_of T); exact (lam_of_recons T hwf ht). qed.

(* The reconstruction predicate is not vacuous at any threshold *)
lemma recons_nonvacuous (T : committee) (s : vec) (p : int -> vec) :
  wf_nodes T => 0 < tthr =>
  exists (lam : int -> rq),
    recons T lam /\ vmap (fun i => lam i ** shr s p i) T = s.
proof.
move=> hwf ht; exists (lam_of T); split.
+ exact (lam_of_recons T hwf ht).
exact (shr_recons_constructed T s p hwf ht).
qed.
