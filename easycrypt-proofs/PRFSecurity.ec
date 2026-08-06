require import AllCore Int List Distr FMap.
require import Params Types Masking.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

module type PRFOracle = {
  proc f(x : view) : vec
}.

module type PRFDistinguisher (F : PRFOracle) = {
  proc distinguish() : bool
}.

module RealPRF = {
  var k : seed

  proc init() : unit = { k <$ dseed; }
  proc f(x : view) : vec = { return prf k x; }
}.

module IdealPRF = {
  var m : (view, vec) fmap

  proc init() : unit = { m <- empty; }

  proc f(x : view) : vec = {
    var r : vec;
    if (x \notin m) {
      r <$ dvec;
      m.[x] <- r;
    }
    return oget m.[x];
  }
}.

module INDReal (D : PRFDistinguisher) = {
  proc main() : bool = {
    var b : bool;
    RealPRF.init();
    b <@ D(RealPRF).distinguish();
    return b;
  }
}.

module INDIdeal (D : PRFDistinguisher) = {
  proc main() : bool = {
    var b : bool;
    IdealPRF.init();
    b <@ D(IdealPRF).distinguish();
    return b;
  }
}.

(* A single fresh ideal query *)
module SingleQuery = {
  proc query(x : view) : vec = {
    var m : (view, vec) fmap;
    var r : vec;
    m <- empty;
    if (x \notin m) {
      r <$ dvec;
      m.[x] <- r;
    }
    return oget m.[x];
  }

  proc uniform(x : view) : vec = {
    var z : vec;
    z <$ dvec;
    return z;
  }
}.

(* Fresh ideal queries sample uniformly *)
equiv single_query_uniform : SingleQuery.query ~ SingleQuery.uniform : ={x} ==> ={res}.
proof.
proc.
rcondt{1} 2.
+ by move=> &hr; auto => />; rewrite mem_empty.
wp; rnd; auto => />.
by smt(get_set_sameE).
qed.

