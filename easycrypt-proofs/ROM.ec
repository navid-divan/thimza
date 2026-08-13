require import AllCore Int List Distr FMap FSet.
require import Params Types Assumptions.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

(* The challenge space of the Fiat Shamir transform *)
op dchal : rq distr = dRq.

(* The challenge distribution is lossless *)
lemma dchal_ll : is_lossless dchal.
proof. exact dRq_ll. qed.

(* The challenge distribution is full *)
lemma dchal_fu : is_full dchal.
proof. exact dRq_fu. qed.

(* The challenge distribution is functionally uniform *)
lemma dchal_funi : is_funiform dchal.
proof. by apply is_full_funiform; [exact dRq_fu | exact dRq_uni]. qed.

type chalquery = vec * vec * msg.

module type ChalRO = {
  proc init() : unit
  proc h(q : chalquery) : rq
  proc set(q : chalquery, c : rq) : unit
  proc dom() : chalquery fset
}.

module LazyChalRO : ChalRO = {
  var m : (chalquery, rq) fmap

  proc init() : unit = { m <- empty; }

  proc h(q : chalquery) : rq = {
    var c : rq;
    if (q \notin m) {
      c <$ dchal;
      m.[q] <- c;
    }
    return oget m.[q];
  }

  proc set(q : chalquery, c : rq) : unit = { m.[q] <- c; }

  proc dom() : chalquery fset = { return fdom m; }
}.

(* A programmed point is returned by the oracle *)
lemma ro_set_get (q0 : chalquery) (c0 : rq) :
  hoare[LazyChalRO.set : q = q0 /\ c = c0 ==> LazyChalRO.m.[q0] = Some c0].
proof. by proc; auto => />; smt(get_set_sameE). qed.

(* Programming one point leaves the others untouched *)
lemma ro_set_other (q0 q1 : chalquery) (c0 : rq) (r1 : rq option) :
  q1 <> q0 =>
  hoare[LazyChalRO.set :
        q = q0 /\ c = c0 /\ LazyChalRO.m.[q1] = r1 ==> LazyChalRO.m.[q1] = r1].
proof. by move=> hne; proc; auto => />; smt(get_setE). qed.

module ROQuery = {
  proc fresh(q : chalquery) : rq = {
    var m : (chalquery, rq) fmap;
    var c : rq;
    m <- empty;
    if (q \notin m) {
      c <$ dchal;
      m.[q] <- c;
    }
    return oget m.[q];
  }

  proc uniform() : rq = {
    var c : rq;
    c <$ dchal;
    return c;
  }
}.

(* A first oracle query returns a uniform challenge *)
equiv ro_fresh_uniform : ROQuery.fresh ~ ROQuery.uniform : true ==> ={res}.
proof.
proc.
rcondt{1} 2; first by move=> &hr; auto => />; smt(mem_empty).
wp; rnd; auto => />.
smt(get_set_sameE).
qed.

(* The oracle is deterministic on repeated queries *)
module ROTwice = {
  proc twice(q : chalquery) : rq * rq = {
    var m : (chalquery, rq) fmap;
    var c, c1, c2 : rq;
    m <- empty;
    if (q \notin m) { c <$ dchal; m.[q] <- c; }
    c1 <- oget m.[q];
    if (q \notin m) { c <$ dchal; m.[q] <- c; }
    c2 <- oget m.[q];
    return (c1, c2);
  }
}.

(* Repeated queries to the oracle agree *)
hoare ro_deterministic : ROTwice.twice : true ==> res.`1 = res.`2.
proof.
proc.
rcondt 2; first by auto => />; smt(mem_empty).
rcondf 5; first by auto => />; smt(mem_set).
by auto.
qed.
