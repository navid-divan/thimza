require import AllCore Int List Distr FSet.
require import Params Types BigOps Sharing Masking.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

(* The signers an adversary has statically corrupted *)
type corrset = int list.

(* A corruption set is admissible below the threshold *)
pred admissible (C : corrset) = uniq C /\ size C <= tthr - 1.

(* The honest members of a committee *)
op honest (T : committee) (C : corrset) : committee =
  filter (fun i => !(i \in C)) T.

(* The corrupted members of a committee *)
op corrupted (T : committee) (C : corrset) : committee =
  filter (fun i => i \in C) T.

(* A committee splits into its honest and corrupted parts *)
lemma honest_corrupted_split (T : committee) (C : corrset) (g : int -> vec) :
  vmap g (honest T C) + vmap g (corrupted T C) = vmap g T.
proof.
rewrite /honest /corrupted.
elim T => [| a T ih] //=.
+ by rewrite !vmap_nil; smt(RqVec.Vector.ZModule.add0r).
case: (a \in C) => hc //=.
+ rewrite !vmap_cons -ih.
  by smt(RqVec.Vector.ZModule.addrCA).
rewrite !vmap_cons -ih.
by smt(RqVec.Vector.ZModule.addrA).
qed.

(* Honest and corrupted membership are mutually exclusive *)
lemma honest_not_corrupted (T : committee) (C : corrset) (i : int) :
  i \in honest T C => !(i \in corrupted T C).
proof. by rewrite /honest /corrupted !mem_filter => -[h _]; smt(mem_filter). qed.

(* Every committee member is honest or corrupted *)
lemma honest_or_corrupted (T : committee) (C : corrset) (i : int) :
  i \in T => i \in honest T C \/ i \in corrupted T C.
proof. by move=> hi; rewrite /honest /corrupted !mem_filter; smt(). qed.

(* An admissible corruption leaves at least one honest signer *)
lemma honest_nonempty (T : committee) (C : corrset) :
  admissible C => uniq T => size T = tthr => 0 < tthr => 0 < size (honest T C).
proof.
move=> [huC hszC] huT hszT ht.
rewrite /honest size_filter.
have hcount : count (fun i => i \in C) T <= size C.
+ rewrite -(size_filter (fun i => i \in C) T).
  apply uniq_leq_size; first by apply filter_uniq.
  by move=> x; rewrite mem_filter => -[].
have hpc := count_predC (fun (i : int) => i \in C) T.
have hcp : count (predC (fun (i : int) => i \in C)) T = count (fun i => !(i \in C)) T.
+ by apply eq_count => x; rewrite /predC.
smt().
qed.

(* The corrupted signers never learn the unmatched pairwise seed *)
lemma mask_unmatched (T : committee) (C : corrset) (vw : view) (i j : int) :
  i \in honest T C => j \in honest T C => i <> j =>
  term T vw i j + term T vw j i = zerov.
proof. by move=> _ _ _; exact (term_anti T vw i j). qed.

(* Honest responses aggregate to the unmasked honest sum *)
lemma honest_agg (T : committee) (vw : view) (g : int -> vec) :
  vmap (fun i => g i + mask T vw i) T = vmap g T.
proof. exact (mask_agg T vw g). qed.

module Corrupt = {
  var cset : int list

  proc init() : unit = { cset <- []; }

  proc corrupt(i : int) : bool = {
    var ok : bool;
    ok <- size cset < tthr - 1 /\ !(i \in cset);
    if (ok) { cset <- i :: cset; }
    return ok;
  }
}.

(* The corruption oracle never exceeds the threshold *)
hoare corrupt_bounded :
  Corrupt.corrupt : uniq Corrupt.cset /\ size Corrupt.cset <= tthr - 1
                    ==> uniq Corrupt.cset /\ size Corrupt.cset <= tthr - 1.
proof. by proc; auto => />; smt(). qed.

(* Initialising the corruption oracle is admissible *)
hoare corrupt_init : Corrupt.init : true ==> admissible Corrupt.cset.
proof. by proc; auto => />; rewrite /admissible /=; smt(thr_range). qed.
