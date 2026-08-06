require import AllCore Int List Distr.
require import Params.

(* Committee size upper bound for the deployment *)
op nmax : { int | 1 <= nmax } as ge1_nmax.

(* Reconstruction threshold of the scheme *)
op tthr : { int | 1 <= tthr <= nmax } as thr_range.

(* Messages signed by the scheme *)
type msg.

(* Round one commitment values *)
type cmt.

(* Transcript views bound to a signing session *)
type view.

(* Pairwise masking seeds are ring vectors *)
type seed = vec.

(* Uniform distribution over PRF seeds *)
op dseed : seed distr = dvec.

(* Seed distribution is lossless *)
lemma dseed_ll : is_lossless dseed.
proof. exact dvec_ll. qed.

(* Seed distribution is full *)
lemma dseed_fu : is_full dseed.
proof. exact dvec_fu. qed.

(* Seed distribution is functionally uniform *)
lemma dseed_funi : is_funiform dseed.
proof. exact dvec_funi. qed.

(* Committee index sets as integer lists *)
type committee = int list.

(* Evaluation points of the Shamir sharing polynomial *)
op alpha : int -> rq.

(* Well formed committees are duplicate free *)
pred wf_committee (T : committee) = uniq T /\ size T = tthr.
