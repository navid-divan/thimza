require import AllCore Int List Distr DList Real.
require import Params Types Protocol Extract.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

type key.

op dkey : key distr.

op prfk : key -> view -> vec.

op drf : (view -> vec) distr.

module type PRFOracle = { proc f(x : view) : vec }.

module type PRFAdv (O : PRFOracle) = { proc guess() : bool }.

module PRFReal = {
  var k : key
  proc init() : unit = { k <$ dkey; }
  proc f(x : view) : vec = { return prfk k x; }
}.

module PRFIdeal = {
  var g : view -> vec
  proc init() : unit = { g <$ drf; }
  proc f(x : view) : vec = { return g x; }
}.

module PRFGame (A : PRFAdv) = {
  proc real() : bool = { var b; PRFReal.init(); b <@ A(PRFReal).guess(); return b; }
  proc ideal() : bool = { var b; PRFIdeal.init(); b <@ A(PRFIdeal).guess(); return b; }
}.

op dkeyv : vec distr.

op dkeyr : row distr.

op dnv : vec distr.

op dnr : row distr.

op dchal : rq distr.

type hintv = rq * vec * row.

module type HintAdv = { proc guess(b : row, hs : hintv list) : bool }.

module HintMLWE (A : HintAdv) = {
  proc mkh(s : vec, e : row) : hintv = {
    var c, r, ep;
    c <$ dchal;
    r <$ dnv;
    ep <$ dnr;
    return (c, c ** s + r, rowZ c e + ep);
  }

  proc real(nq : int) : bool = {
    var s, e, hs, h, i, bit;
    s <$ dkeyv;
    e <$ dkeyr;
    hs <- [];
    i <- 0;
    while (i < nq) { h <@ mkh(s, e); hs <- rcons hs h; i <- i + 1; }
    bit <@ A.guess(mulA mA s + e, hs);
    return bit;
  }

  proc ideal(nq : int) : bool = {
    var s, e, b, hs, h, i, bit;
    s <$ dkeyv;
    e <$ dkeyr;
    b <$ drow;
    hs <- [];
    i <- 0;
    while (i < nq) { h <@ mkh(s, e); hs <- rcons hs h; i <- i + 1; }
    bit <@ A.guess(b, hs);
    return bit;
  }
}.

op dG : (row -> row * msg -> rq) distr.

module GO = {
  var g : row -> row * msg -> rq
  proc init() : unit = { g <$ dG; }
  proc h(y : row, a : row * msg) : rq = { return g y a; }
}.

module type GOracle = { proc h(y : row, a : row * msg) : rq }.

module type STAdv (G : GOracle) = { proc solve(b : row) : row * msg * vec * rq * row }.

module STMSIS (A : STAdv) = {
  proc main() : bool = {
    var b, vk, mu, z, c, u;
    GO.init();
    b <$ drow;
    (vk, mu, z, c, u) <@ A(GO).solve(b);
    return GO.g (stimage vk z c u) (vk, mu) = c /\ solnorm z c u <= bst;
  }
}.
