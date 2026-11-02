require import AllCore Int List Distr DList FMap FSet Real RealExp Finite.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption.
require import Protocol Notions Privacy Extract FinEnum.
require QROM ExtRO.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

op enum_msg : msg list.

axiom enum_msg_spec : forall (m : msg), count (pred1 m) enum_msg = 1.

type h1in.

op enum_h1in : h1in list.

axiom enum_h1in_spec : forall (x : h1in), count (pred1 x) enum_h1in = 1.

op e1 : row -> msg -> committee -> cmt list -> h1in.

op dcmt : cmt distr.

axiom dcmt_ll : is_lossless dcmt.

axiom dcmt_uni : is_uniform dcmt.

op dview : view distr.

axiom dview_ll : is_lossless dview.

axiom dview_uni : is_uniform dview.

op dchal : rq distr.

axiom dchal_ll : is_lossless dchal.

axiom dchal_uni : is_uniform dchal.

axiom dnonce_ll : is_lossless dnonce.

axiom dnoiser_ll : is_lossless dnoiser.

op dskey : vec distr.

axiom dskey_ll : is_lossless dskey.

op dekey : row distr.

axiom dekey_ll : is_lossless dekey.

op rndkey : row -> row.

op qh0 : { int | 0 <= qh0 } as ge0_qh0.

op qh1 : { int | 0 <= qh1 } as ge0_qh1.

op qhc : { int | 0 <= qhc } as ge0_qhc.

op qsig : { int | 0 <= qsig } as ge0_qsig.

type h0key = (row * msg) * pidx.

type h0in = h0key * row.

type hcin = row * (row * msg).

op enum_h0key : h0key list =
  allpairs (fun a b => (a, b)) (allpairs (fun a b => (a, b)) enum_row enum_msg) enum_pidx.

op enum_h0in : h0in list = allpairs (fun a b => (a, b)) enum_h0key enum_row.

op enum_hcin : hcin list =
  allpairs (fun a b => (a, b)) enum_row (allpairs (fun a b => (a, b)) enum_row enum_msg).

op enum_pair : (pidx * pidx) list = allpairs (fun a b => (a, b)) enum_pidx enum_pidx.

(* Commitment hash inputs are finite *)
lemma enum_h0in_spec : forall (x : h0in), count (pred1 x) enum_h0in = 1.
proof.
apply enum_pair; last by exact enum_row_spec.
apply enum_pair; last by exact enum_pidx_spec.
by apply enum_pair; [exact enum_row_spec | exact enum_msg_spec].
qed.

(* Challenge hash inputs are finite *)
lemma enum_hcin_spec : forall (x : hcin), count (pred1 x) enum_hcin = 1.
proof.
apply enum_pair; first by exact enum_row_spec.
by apply enum_pair; [exact enum_row_spec | exact enum_msg_spec].
qed.

(* Index pairs are finite *)
lemma enum_pair_spec : forall (x : pidx * pidx), count (pred1 x) enum_pair = 1.
proof. by apply enum_pair; exact enum_pidx_spec. qed.

(* Nonces are lossless *)
lemma dnp_ll : is_lossless (dnonce `*` dnoiser).
proof. by apply dprod_ll; split; [exact dnonce_ll | exact dnoiser_ll]. qed.

clone QROM.QROMLazy as H0H with
  type key <- h0key,
  type pt <- row,
  type sec <- vec * row,
  type side <- vec * row,
  type hash <- cmt,
  op dsec <- dnonce `*` dnoiser,
  op popn <- (fun (s : vec * row) => rndc (commit s.`1 s.`2)),
  op dhash <- dcmt,
  op enum <- enum_h0in
  proof dsec_ll by exact dnp_ll
  proof dhash_ll by exact dcmt_ll
  proof dhash_uni by exact dcmt_uni
  proof enum_spec by exact enum_h0in_spec.

clone ExtRO.ExtRO as H0C with
  type from <- h0in,
  type hash <- cmt,
  type side <- vec * row,
  op dhash <- dcmt,
  op enum <- enum_h0in
  proof dhash_ll by exact dcmt_ll
  proof dhash_uni by exact dcmt_uni
  proof enum_spec by exact enum_h0in_spec.

clone QROM.QROM as H1O with
  type from <- h1in,
  type hash <- view,
  type side <- vec * row,
  op dhash <- dview,
  op enum <- enum_h1in
  proof dhash_ll by exact dview_ll
  proof dhash_uni by exact dview_uni
  proof enum_spec by exact enum_h1in_spec.

clone QROM.QROM as HCO with
  type from <- hcin,
  type hash <- rq,
  type side <- vec * row,
  op dhash <- dchal,
  op enum <- enum_hcin
  proof dhash_ll by exact dchal_ll
  proof dhash_uni by exact dchal_uni
  proof enum_spec by exact enum_hcin_spec.

clone MUniFinFun as PF with
  type t <- pidx * pidx,
  op FinT.enum <- enum_pair
  proof FinT.enum_spec by exact enum_pair_spec
  proof *.

op dseedf : (pidx * pidx -> seed) distr = PF.dfun (fun _ => dseed).

op dpoly : (int -> vec) distr =
  dmap (dlist dvec (tthr - 1)) (fun l => fun u => if 1 <= u < tthr then nth RqVec.Vector.zerov l (u - 1) else RqVec.Vector.zerov).

op admc (C : corrset) : bool = uniq C /\ size C <= tthr - 1 /\ all (fun j => 1 <= j <= nmax) C.

op h0of (f : h0in -> cmt) : h0fun = fun vk mu i w => f (((vk, mu), toidx i), w).

op h1of (f : h1in -> view) : h1fun = fun vk mu T cs => f (e1 vk mu T cs).

op hcof (f : hcin -> rq) : hcfun = fun vk w mu => f (liftw w, (vk, mu)).

op amask (pv : int -> int -> vec) (T : committee) (i : int) : vec =
  vmap (fun j => if i = j then RqVec.Vector.zerov else if i < j then pv i j else - pv j i) T.

op hpair (C : corrset) (a b : int) : bool = !(a \in C) /\ !(b \in C).

op mixsd (C : corrset) (sh sc : pidx * pidx -> seed) : pidx * pidx -> seed =
  fun ab => if hpair C (PIdx.val ab.`1) (PIdx.val ab.`2) then sh ab else sc ab.

op seedpv (sd : pidx * pidx -> seed) (vw : view) : int -> int -> vec =
  fun a b => prf (sd (toidx a, toidx b)) vw.

(* Seeds on a partition combine to uniform seeds *)
lemma dseedf_split (P : pidx * pidx -> bool) :
  dlet dseedf (fun f => dmap dseedf (fun g => fun x => if P x then f x else g x)) = dseedf.
proof.
have -> : (fun f => dmap dseedf (fun g => fun x => if P x then f x else g x))
        = (fun (f : pidx * pidx -> seed) =>
             PF.dfun (fun x => (fun (x : pidx * pidx) (v : seed) => if P x then dunit v else dseed) x (f x))).
+ apply fun_ext => f /=.
  rewrite /dseedf (PF.dmap_dfun (fun _ => dseed) (fun x gx => if P x then f x else gx)) /=.
  congr; apply fun_ext => x /=.
  case: (P x) => hP; first by rewrite dmap_cst // dseed_ll.
  by rewrite dmap_id.
rewrite {1}/dseedf PF.dlet_dfun /=.
rewrite /dseedf; congr; apply fun_ext => x /=.
case: (P x) => hP.
+ have -> : (fun (v : seed) => dunit v) = MUnit.dunit by done.
  by rewrite dlet_d_unit.
by rewrite dlet_cst // dseed_ll.
qed.

module type HOr = {
  proc h0(x : h0in) : cmt
  proc h1(x : h1in) : view
  proc hc(x : hcin) : rq
}.

module type SOr = {
  proc o1(i : int, mu : msg) : (int * cmt) option
  proc o2(u : int, T : committee, cs : cmt list) : row option
  proc o3(u : int, T : committee, cs : cmt list, ws : row list) : vec option
}.

module type Adv (H : HOr) (O : SOr) = {
  proc corrupt() : corrset {}
  proc forge(vk : row, sks : int -> vec, sds : pidx * pidx -> seed) : msg * sig
}.

module Cnt = {
  var c0 : int
  var c1 : int
  var cc : int
  var cs : int
}.

module CntH (H : HOr) : HOr = {
  proc h0(x : h0in) : cmt = { var y; Cnt.c0 <- Cnt.c0 + 1; y <@ H.h0(x); return y; }
  proc h1(x : h1in) : view = { var y; Cnt.c1 <- Cnt.c1 + 1; y <@ H.h1(x); return y; }
  proc hc(x : hcin) : rq = { var y; Cnt.cc <- Cnt.cc + 1; y <@ H.hc(x); return y; }
}.

module CntO (O : SOr) : SOr = {
  proc o1(i : int, mu : msg) : (int * cmt) option = {
    var r; Cnt.cs <- Cnt.cs + 1; r <@ O.o1(i, mu); return r;
  }
  proc o2(u : int, T : committee, cs : cmt list) : row option = {
    var r; Cnt.cs <- Cnt.cs + 1; r <@ O.o2(u, T, cs); return r;
  }
  proc o3(u : int, T : committee, cs : cmt list, ws : row list) : vec option = {
    var r; Cnt.cs <- Cnt.cs + 1; r <@ O.o3(u, T, cs, ws); return r;
  }
}.

module S = {
  var cs   : corrset
  var s    : vec
  var e    : row
  var p    : int -> vec
  var t    : row
  var sdh  : pidx * pidx -> seed
  var sdc  : pidx * pidx -> seed
  var toks : (int, token) fmap
  var req  : (int, request) fmap
  var ctr  : int
  var lo   : alog
  var lr   : alog
}.
