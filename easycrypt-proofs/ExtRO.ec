require import AllCore Int List Distr Real RealExp.
require QROM.

abstract theory ExtRO.

clone include QROM.QROM.

type sst.

op sinit : sst distr.

axiom sinit_ll : is_lossless sinit.

op sro : sst -> from -> sst * hash.

op sext : sst -> hash -> sst * from option.

module Sim = {
  var st : sst

  proc init() : unit = { st <$ sinit; }

  proc h(x : from) : hash = {
    var y;
    (st, y) <- sro st x;
    return y;
  }

  proc ext(t : hash) : from option = {
    var r;
    (st, r) <- sext st t;
    return r;
  }
}.

module type ExtO = {
  proc h(x : from) : hash
  proc submit(t : hash) : unit
  proc check(k : int, x : from) : hash
}.

module ER : ExtO = {
  var ts  : hash list
  var xs  : from option list
  var cks : (int * from * hash) list
  var simw : bool

  proc h(x : from) : hash = {
    var y;
    CQ.n <- CQ.n + 1;
    if (simw) { y <@ Sim.h(x); } else { y <- QRO.fh x; }
    return y;
  }

  proc submit(t : hash) : unit = {
    var r;
    ts <- rcons ts t;
    if (simw) { r <@ Sim.ext(t); xs <- rcons xs r; } else { xs <- rcons xs None; }
  }

  proc check(k : int, x : from) : hash = {
    var y;
    y <@ h(x);
    cks <- rcons cks (k, x, y);
    return y;
  }
}.

module type AdvExt (O : ExtO) = { proc main() : bool }.

module EG (A : AdvExt) = {
  proc main(b : bool) : bool = {
    var r;
    QRO.init();
    Sim.init();
    ER.ts <- [];
    ER.xs <- [];
    ER.cks <- [];
    ER.simw <- b;
    CQ.n <- 0;
    r <@ A(ER).main();
    return r;
  }
}.

op extbad (ts : hash list) (xs : from option list) (cks : (int * from * hash) list) : bool =
  exists e, e \in cks /\ 0 <= e.`1 < size ts
            /\ nth None xs e.`1 <> Some e.`2 /\ e.`3 = nth witness ts e.`1.

(* Extraction barely disturbs the simulated oracle *)
axiom ext_sim (A <: AdvExt {-QRO, -CQ, -Sim, -ER}) &m (q l : int) :
  0 <= q => 0 <= l =>
  hoare [A(ER).main : CQ.n = 0 /\ ER.ts = [] ==> CQ.n <= q /\ size ER.ts <= l] =>
  `|Pr[EG(A).main(false) @ &m : res] - Pr[EG(A).main(true) @ &m : res]|
    <= 8%r * l%r * (q + l)%r * sqrt (2%r * p_max dhash).

(* Accepted openings match the extracted ones *)
axiom ext_sound (A <: AdvExt {-QRO, -CQ, -Sim, -ER}) &m (q l : int) :
  0 <= q => 0 <= l =>
  hoare [A(ER).main : CQ.n = 0 /\ ER.ts = [] ==> CQ.n <= q /\ size ER.ts <= l] =>
  Pr[EG(A).main(true) @ &m : extbad ER.ts ER.xs ER.cks]
    <= 8%r * l%r * (q + 1)%r * sqrt (2%r * p_max dhash)
       + (40%r * exp 1%r ^ 2 * (q + l + 1)%r ^ 3 + 2%r) * p_max dhash.

end ExtRO.
