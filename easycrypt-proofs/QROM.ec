require import AllCore Int List Distr Real RealExp FMap FSet.

abstract theory QROM.

type from.

type hash.

type side.

op dhash : hash distr.

axiom dhash_ll : is_lossless dhash.

axiom dhash_uni : is_uniform dhash.

op enum : from list.

axiom enum_spec : forall x, count (pred1 x) enum = 1.

clone import MUniFinFun as MF with
  type t <- from,
  op FinT.enum <- enum
  proof FinT.enum_spec by exact enum_spec
  proof *.

op dfh : (from -> hash) distr = dfun (fun _ => dhash).

(* The oracle distribution is lossless *)
lemma dfh_ll : is_lossless dfh.
proof. by apply dfun_ll => x /=; exact dhash_ll. qed.

(* Fresh reprogramming keeps oracles uniform *)
lemma dfh_reprog (x0 : from) :
  dlet dfh (fun f => dmap dhash (fun y => f.[x0 <- y])) = dfh.
proof.
have := dlet_dfun_update (fun _ => dhash) x0.
by rewrite /= dhash_ll dscalar1.
qed.

(* Partial overwriting keeps oracles uniform *)
lemma dfh_fill (f : from -> hash) (P : from -> bool) :
  dmap dfh (fun g => fun x => if P x then f x else g x)
  = dfun (fun x => if P x then dunit (f x) else dhash).
proof.
rewrite (dmap_dfun (fun _ => dhash) (fun x gx => if P x then f x else gx)) /=.
congr; apply fun_ext => x /=.
case: (P x) => hP.
+ by rewrite dmap_cst // dhash_ll.
by rewrite dmap_id.
qed.

(* Oracles on a partition combine to one oracle *)
lemma dfh_split (P : from -> bool) :
  dlet dfh (fun f => dmap dfh (fun g => fun x => if P x then f x else g x)) = dfh.
proof.
have -> : (fun f => dmap dfh (fun g => fun x => if P x then f x else g x))
        = (fun (f : from -> hash) =>
             dfun (fun x => (fun (x : from) (v : hash) => if P x then dunit v else dhash) x (f x))).
+ by apply fun_ext => f /=; rewrite dfh_fill.
rewrite {1}/dfh dlet_dfun /=.
rewrite /dfh; congr; apply fun_ext => x /=.
case: (P x) => hP.
+ have -> : (fun (v : hash) => dunit v) = MUnit.dunit by done.
  by rewrite dlet_d_unit.
by rewrite dlet_cst // dhash_ll.
qed.

module QRO = {
  var fh : from -> hash

  proc init() : unit = { fh <$ dfh; }

  proc h(x : from) : hash = { return fh x; }
}.

module type QRO_i = { proc h(x : from) : hash }.

module CQ : QRO_i = {
  var n : int

  proc h(x : from) : hash = {
    n <- n + 1;
    return QRO.fh x;
  }
}.

(* Queries are answered by the function *)
hoare cq_answer (x0 : from) : CQ.h : x = x0 ==> res = QRO.fh x0.
proof. by proc; auto. qed.

module type AdvCol (H : QRO_i) = { proc main() : from * from }.

module Col (A : AdvCol) = {
  proc main() : bool = {
    var x1, x2 : from;
    QRO.init();
    CQ.n <- 0;
    (x1, x2) <@ A(CQ).main();
    return x1 <> x2 /\ QRO.fh x1 = QRO.fh x2;
  }
}.

(* Collisions need cube root queries *)
axiom pr_col (A <: AdvCol {-QRO, -CQ}) &m (q : int) :
  hoare [A(CQ).main : CQ.n = 0 ==> CQ.n <= q] =>
  Pr[Col(A).main() @ &m : res] <= 27%r * (q + 2)%r ^ 3 * p_max dhash.

module type Repro_i = { proc reprog(d : (from * side) distr) : from * side }.

module type AdvRep (H : QRO_i) (R : Repro_i) = { proc main() : bool }.

op pmaxok (d : (from * side) distr) (p : real) : bool =
  forall x, mu d (fun (a : from * side) => a.`1 = x) <= p.

module Rep : Repro_i = {
  var cnt : int
  var bnd : int
  var pm  : real
  var wld : bool

  proc reprog(d : (from * side) distr) : from * side = {
    var a, y;
    a <- witness;
    if (cnt < bnd /\ pmaxok d pm) {
      a <$ d;
      y <$ dhash;
      if (wld) { QRO.fh <- QRO.fh.[a.`1 <- y]; }
      cnt <- cnt + 1;
    }
    return a;
  }
}.

module RepG (A : AdvRep) = {
  proc main(b : bool, nr : int, p : real) : bool = {
    var r;
    QRO.init();
    Rep.wld <- b;
    Rep.bnd <- nr;
    Rep.pm <- p;
    Rep.cnt <- 0;
    CQ.n <- 0;
    r <@ A(CQ, Rep).main();
    return r;
  }
}.

(* Unlikely reprogramming is hard to notice *)
axiom ghhm (A <: AdvRep {-QRO, -CQ, -Rep}) &m (q nr : int) (p : real) :
  0 <= q => 0 <= nr => 0%r <= p =>
  hoare [A(CQ, Rep).main : CQ.n = 0 ==> CQ.n <= q] =>
  `|Pr[RepG(A).main(false, nr, p) @ &m : res] - Pr[RepG(A).main(true, nr, p) @ &m : res]|
    <= nr%r * (sqrt (q%r * p) + q%r * p / 2%r).

(* Reprogramming bounds grow with reprogrammings *)
lemma ghhm_mono (q n1 n2 : int) (p : real) :
  0 <= q => 0%r <= p => n1 <= n2 =>
  n1%r * (sqrt (q%r * p) + q%r * p / 2%r) <= n2%r * (sqrt (q%r * p) + q%r * p / 2%r).
proof.
move=> hq hp hn.
have h0 : 0%r <= sqrt (q%r * p) + q%r * p / 2%r.
+ have := ge0_sqrt (q%r * p); smt().
smt().
qed.

end QROM.

abstract theory QROMLazy.

type key.

type pt.

type sec.

op dsec : sec distr.

axiom dsec_ll : is_lossless dsec.

op popn : sec -> pt.

clone include QROM with type from <- key * pt.

module type LC_i = {
  proc h(x : key * pt) : hash
  proc commit(u : int, k : key) : hash
  proc reveal(u : int) : sec
}.

module LC = {
  var sv  : (int, sec) fmap
  var rv  : int list
  var fv  : (int * key, hash) fmap
  var lft : bool

  proc gsec(u : int) : sec = {
    var s;
    if (u \notin sv) { s <$ dsec; sv.[u] <- s; }
    return oget sv.[u];
  }

  proc gf(u : int, k : key) : hash = {
    var y;
    if ((u, k) \notin fv) { y <$ dhash; fv.[(u, k)] <- y; }
    return oget fv.[(u, k)];
  }

  proc h(x : key * pt) : hash = {
    var r, us;
    CQ.n <- CQ.n + 1;
    us <- filter (fun u => u \in sv /\ popn (oget sv.[u]) = x.`2) rv;
    if (lft /\ us <> []) {
      r <@ gf(head 0 us, x.`1);
    } else {
      r <- QRO.fh x;
    }
    return r;
  }

  proc commit(u : int, k : key) : hash = {
    var r, s;
    if (lft) {
      r <@ gf(u, k);
    } else {
      s <@ gsec(u);
      r <- QRO.fh (k, popn s);
    }
    return r;
  }

  proc reveal(u : int) : sec = {
    var s;
    s <@ gsec(u);
    if (!(u \in rv)) { rv <- u :: rv; }
    return s;
  }
}.

module type AdvLC (O : LC_i) = { proc main() : bool }.

module LCG (A : AdvLC) = {
  proc main(b : bool) : bool = {
    var r;
    QRO.init();
    LC.sv <- empty;
    LC.rv <- [];
    LC.fv <- empty;
    LC.lft <- b;
    CQ.n <- 0;
    r <@ A(LC).main();
    return r;
  }
}.

(* Lazily programmed commitments are hard to notice *)
axiom o2h_lazy (A <: AdvLC {-QRO, -CQ, -LC}) &m (q nu : int) (p : real) :
  0 <= q => 0 <= nu => 0%r <= p =>
  (forall w, mu dsec (fun s => popn s = w) <= p) =>
  hoare [A(LC).main : CQ.n = 0 /\ LC.sv = empty ==> CQ.n <= q /\ card (fdom LC.sv) <= nu] =>
  `|Pr[LCG(A).main(true) @ &m : res] - Pr[LCG(A).main(false) @ &m : res]|
    <= 2%r * q%r * sqrt (nu%r * p) + (nu * nu)%r * p.

end QROMLazy.
