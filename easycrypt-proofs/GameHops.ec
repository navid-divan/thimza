require import AllCore Int List Distr Real.
require import Params Types BigOps Masking Assumptions Protocol Combine Verify.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

module St = {
  var sk    : int -> vec
  var lam   : int -> rq
  var nonce : int -> vec
  var tvk   : vec
}.

module type SO = {
  proc sign3(mu : msg, T : committee, vw : view, c : rq, i : int) : vec
}.

module type Ad (O : SO) = {
  proc forge(t : vec) : msg * sig
}.

(* Vector addition regroups to the right *)
lemma vaddA_r (a b c : vec) : a + b + c = a + (b + c).
proof. smt(RqVec.Vector.ZModule.addrA). qed.

(* Hop zero, the honest masked oracle of the real game *)
module O0 : SO = {
  proc sign3(mu : msg, T : committee, vw : view, c : rq, i : int) : vec = {
    var m : vec;
    m <$ dvec;
    return (Rq.( * ) c (St.lam i)) ** St.sk i + St.nonce i + m;
  }
}.

(* Hop one, the nonce dropped from the response *)
module O1 : SO = {
  proc sign3(mu : msg, T : committee, vw : view, c : rq, i : int) : vec = {
    var m : vec;
    m <$ dvec;
    return (Rq.( * ) c (St.lam i)) ** St.sk i + m;
  }
}.

(* Hop two, the response drawn uniformly at random *)
module O2 : SO = {
  proc sign3(mu : msg, T : committee, vw : view, c : rq, i : int) : vec = {
    var m : vec;
    m <$ dvec;
    return m;
  }
}.

module G (O : SO) (A : Ad) = {
  proc main() : bool = {
    var mu : msg;
    var sg : sig;
    var c, z, h;
    (mu, sg) <@ A(O).forge(St.tvk);
    (c, z, h) <- sg;
    return vrfy St.tvk mu (c, z, h);
  }
}.

(* The real response is a uniform value *)
equiv hop02 : O0.sign3 ~ O2.sign3 : ={glob St, mu, T, vw, c, i} ==> ={res}.
proof.
proc.
rnd (fun (m : vec) =>
       (Rq.( * ) c{1} (St.lam{1} i{1})) ** St.sk{1} i{1} + St.nonce{1} i{1} + m)
    (fun (y : vec) =>
       y - ((Rq.( * ) c{1} (St.lam{1} i{1})) ** St.sk{1} i{1} + St.nonce{1} i{1})).
skip => &1 &2 _ /=; split.
+ by move=> y hy; rewrite vaddS.
move=> _; split.
+ by move=> y hy; apply dvec_funi.
move=> _ m hm; split; first exact dvec_fu.
by move=> _; rewrite vsubK.
qed.

(* The keyed response without the nonce is also uniform *)
equiv hop12 : O1.sign3 ~ O2.sign3 : ={glob St, mu, T, vw, c, i} ==> ={res}.
proof.
proc.
rnd (fun (m : vec) => (Rq.( * ) c{1} (St.lam{1} i{1})) ** St.sk{1} i{1} + m)
    (fun (y : vec) => y - (Rq.( * ) c{1} (St.lam{1} i{1})) ** St.sk{1} i{1}).
skip => &1 &2 _ /=; split.
+ by move=> y hy; rewrite vaddS.
move=> _; split.
+ by move=> y hy; apply dvec_funi.
move=> _ m hm; split; first exact dvec_fu.
by move=> _; rewrite vsubK.
qed.

(* The real game equals the uniform game *)
lemma pr_hop02 (A <: Ad {-St}) &m :
  Pr[G(O0, A).main() @ &m : res] = Pr[G(O2, A).main() @ &m : res].
proof.
byequiv (: ={glob A, glob St} ==> ={res}) => //.
proc; wp.
call (: ={glob St}); first by conseq hop02.
by auto.
qed.

(* The nonce free game equals the uniform game *)
lemma pr_hop12 (A <: Ad {-St}) &m :
  Pr[G(O1, A).main() @ &m : res] = Pr[G(O2, A).main() @ &m : res].
proof.
byequiv (: ={glob A, glob St} ==> ={res}) => //.
proc; wp.
call (: ={glob St}); first by conseq hop12.
by auto.
qed.

(* Dropping the nonce does not change the winning probability *)
lemma pr_hop01 (A <: Ad {-St}) &m :
  Pr[G(O0, A).main() @ &m : res] = Pr[G(O1, A).main() @ &m : res].
proof. by rewrite (pr_hop02 A &m) (pr_hop12 A &m). qed.

(* The whole sequence of hops is lossless in advantage *)
lemma pr_hops (A <: Ad {-St}) &m :
  Pr[G(O0, A).main() @ &m : res] = Pr[G(O2, A).main() @ &m : res].
proof. exact (pr_hop02 A &m). qed.

(* The real and final oracles are perfectly indistinguishable *)
lemma final_key_free (A <: Ad {-St}) &m :
  `|Pr[G(O0, A).main() @ &m : res] - Pr[G(O2, A).main() @ &m : res]| = 0%r.
proof. by rewrite (pr_hops A &m); smt(). qed.

(* The advantage is bounded by the final game, with no loss *)
lemma advantage_bound (A <: Ad {-St}) &m :
  Pr[G(O0, A).main() @ &m : res] <= Pr[G(O2, A).main() @ &m : res].
proof. by rewrite (pr_hops A &m). qed.

(* The final oracle reads no part of the signing key state *)
equiv o2_key_independent :
  O2.sign3 ~ O2.sign3 : ={mu, T, vw, c, i} ==> ={res}.
proof. by proc; auto. qed.
