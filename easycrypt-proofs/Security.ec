require import AllCore Int List Distr.
require import Params Types Sharing Masking Assumptions Protocol Combine Verify.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

module KeyState = {
  var sk    : int -> vec
  var lam   : int -> rq
  var nonce : int -> vec
  var tvk   : vec
}.

module type SignOracle = {
  proc sign3(mu : msg, T : committee, vw : view, c : rq, i : int) : vec
}.

module type Adv (O : SignOracle) = {
  proc forge(t : vec) : msg * sig
}.

module type Forger = {
  proc forge(t : vec) : msg * sig
}.

(* The real honestly masked signing oracle *)
module OReal : SignOracle = {
  proc sign3(mu : msg, T : committee, vw : view, c : rq, i : int) : vec = {
    var m : vec;
    m <$ dvec;
    return (Rq.( * ) c (KeyState.lam i)) ** KeyState.sk i + KeyState.nonce i + m;
  }
}.

(* The simulated uniform signing oracle *)
module OSim : SignOracle = {
  proc sign3(mu : msg, T : committee, vw : view, c : rq, i : int) : vec = {
    var z : vec;
    z <$ dvec;
    return z;
  }
}.

module Game (O : SignOracle) (A : Adv) = {
  proc main() : bool = {
    var mu : msg;
    var sg : sig;
    var c, z, h;
    (mu, sg) <@ A(O).forge(KeyState.tvk);
    (c, z, h) <- sg;
    return vrfy KeyState.tvk mu (c, z, h);
  }
}.

module GameUF (F : Forger) = {
  proc main() : bool = {
    var mu : msg;
    var sg : sig;
    var c, z, h;
    (mu, sg) <@ F.forge(KeyState.tvk);
    (c, z, h) <- sg;
    return vrfy KeyState.tvk mu (c, z, h);
  }
}.

module B (A : Adv) : Forger = {
  proc forge(t : vec) : msg * sig = {
    var r : msg * sig;
    r <@ A(OSim).forge(t);
    return r;
  }
}.

(* Masked responses are uniformly distributed *)
equiv oracle_sim : OReal.sign3 ~ OSim.sign3 :
  ={glob KeyState, mu, T, vw, c, i} ==> ={res}.
proof.
proc.
rnd (fun (m : vec) =>
       (Rq.( * ) c{1} (KeyState.lam{1} i{1})) ** KeyState.sk{1} i{1} + KeyState.nonce{1} i{1} + m)
    (fun (y : vec) =>
       y - ((Rq.( * ) c{1} (KeyState.lam{1} i{1})) ** KeyState.sk{1} i{1} + KeyState.nonce{1} i{1})).
skip => &1 &2 _ /=; split.
+ by move=> y hy; rewrite vaddS.
move=> _; split.
+ by move=> y hy; apply dvec_funi.
move=> _ m hm; split; first exact dvec_fu.
by move=> _; rewrite vsubK.
qed.

(* Real and simulated oracles are indistinguishable *)
lemma tsufca_sim (A <: Adv {-KeyState}) &m :
  Pr[Game(OReal, A).main() @ &m : res] = Pr[Game(OSim, A).main() @ &m : res].
proof.
byequiv (: ={glob A, glob KeyState} ==> ={res}) => //.
proc.
wp.
call (: ={glob KeyState}); first by conseq oracle_sim.
by auto.
qed.

(* Channel agnostic unforgeability reduces to core *)
lemma tsufca_reduction (A <: Adv {-KeyState}) &m :
  Pr[Game(OReal, A).main() @ &m : res] = Pr[GameUF(B(A)).main() @ &m : res].
proof.
rewrite (tsufca_sim A &m).
byequiv (: ={glob A, glob KeyState} ==> ={res}) => //.
proc.
inline B(A).forge.
wp.
call (: ={glob KeyState}); first by proc; auto.
by auto.
qed.

(* The two oracles are indistinguishable *)
lemma oracle_sim_information_theoretic (A <: Adv {-KeyState}) &m :
  `|Pr[Game(OReal, A).main() @ &m : res] - Pr[Game(OSim, A).main() @ &m : res]| = 0%r.
proof. by rewrite (tsufca_sim A &m); smt(). qed.
