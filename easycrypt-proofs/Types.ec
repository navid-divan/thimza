require import AllCore Int List Distr.
require import Params.

op nmax : { int | 1 <= nmax } as ge1_nmax.

op tthr : { int | 1 <= tthr <= nmax } as thr_range.

type msg.

type cmt.

type view.

type seed = vec.

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

type committee = int list.

op alpha : int -> rq.

pred wf_committee (T : committee) = uniq T /\ size T = tthr.
