require import AllCore Int List Distr.
require import Params Types Sharing Masking Assumptions Protocol Combine Verify.
import RqVec RqVec.Vector RqVec.Vector.ZModule.

module type Sign3Oracle = {
  proc sign3(mu : msg, T : committee, vw : view, c : rq, i : int) : vec
}.

(* The weakest oracle level *)
module type UF0Oracle = {
  proc query(mu : msg) : sig
}.

(* The strongest oracle level *)
module type UF4Oracle = {
  proc sign3(mu : msg, T : committee, vw : view, c : rq, i : int) : vec
  proc corrupt(i : int) : seed * vec
  proc network(m : view) : cmt list * vec list
}.

module type Forger0 (O : UF0Oracle) = {
  proc forge(t : vec) : msg * sig
}.

module type Forger4 (O : UF4Oracle) = {
  proc forge(t : vec) : msg * sig
}.

module Setup = {
  var tvk : vec
}.

(* The TS UF 0 experiment *)
module GameUF0 (O : UF0Oracle) (F : Forger0) = {
  proc main() : bool = {
    var mu : msg;
    var sg : sig;
    var c, z, h;
    (mu, sg) <@ F(O).forge(Setup.tvk);
    (c, z, h) <- sg;
    return vrfy Setup.tvk mu (c, z, h);
  }
}.

(* The TS UF CA experiment *)
module GameUF4 (O : UF4Oracle) (F : Forger4) = {
  proc main() : bool = {
    var mu : msg;
    var sg : sig;
    var c, z, h;
    (mu, sg) <@ F(O).forge(Setup.tvk);
    (c, z, h) <- sg;
    return vrfy Setup.tvk mu (c, z, h);
  }
}.

(* Singleton committees degenerate to ordinary signing *)
op singleton (i : int) : committee = [i].

(* Trivial singleton reconstruction coefficient *)
op lamSingle : int -> rq = fun _ => Rq.oner.

(* Singleton committees are well formed *)
lemma singleton_wf (i : int) : tthr = 1 => wf_committee (singleton i).
proof. by move=> ht; rewrite /wf_committee /singleton ht /=. qed.

(* Singleton share is the master secret *)
lemma singleton_share (s0 : vec) (p : int -> vec) (i : int) :
  tthr = 1 => shr s0 p i = s0.
proof. exact (shr_share0 s0 p i). qed.

(* Singleton signers need no partners *)
lemma singleton_no_partners (i : int) :
  partners (singleton i) i = [].
proof. by rewrite /partners /singleton /predC1 /=. qed.

(* Singleton committees contribute no mask *)
lemma singleton_mask_zero (vw : view) (i : int) :
  mask (singleton i) vw i = zerov.
proof.
rewrite (mask_partners (singleton i) vw i) singleton_no_partners.
exact vmap_nil.
qed.

(* Singleton response matches ordinary signing *)
lemma singleton_response (c : rq) (s0 : vec) (p r : int -> vec) (vw : view) (i : int) :
  tthr = 1 =>
  zcomb (singleton i) (fun j => (Rq.( * ) c (lamSingle j)) ** shr s0 p j + r j + mask (singleton i) vw j)
  = c ** s0 + r i.
proof.
move=> ht.
rewrite /zcomb /singleton vmap_cons vmap_nil /=.
have e1 : shr s0 p i = s0 by exact (singleton_share s0 p i ht).
have e2 : mask (singleton i) vw i = zerov by exact (singleton_mask_zero vw i).
rewrite e1 e2.
smt(RqVec.Vector.ZModule.addr0).
qed.
