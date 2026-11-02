require import AllCore Int List Distr DList FMap.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption Protocol Notions Privacy.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

op rndt : row -> row.

op dsecret : vec distr.

op derr : row distr.

op dpoly : (int -> vec) distr.

op dh0 : h0fun distr.

op dh1 : h1fun distr.

op dhc : hcfun distr.

op cadm (C : corrset) : bool = uniq C /\ size C <= tthr - 1.

module type HOracles = {
  proc h0(x : row * msg * int * row) : cmt
  proc h1(x : row * msg * committee * cmt list) : view
  proc hc(x : row * row * msg) : rq
}.

module type TOracles = {
  proc o1(i : int, mu : msg) : (int * cmt) option
  proc o2(u : int, T : committee, cs : cmt list) : row option
  proc o3(u : int, T : committee, cs : cmt list, ws : row list) : vec option
}.

module type Adv (H : HOracles) (O : TOracles) = {
  proc corrupt() : corrset {}
  proc forge(vk : row, sks : int -> vec) : msg * sig
}.

module St = {
  var h0   : h0fun
  var h1   : h1fun
  var hc   : hcfun
  var vk   : row
  var s    : vec
  var p    : int -> vec
  var cs   : corrset
  var toks : (int, token) fmap
  var req  : (int, request) fmap
  var ctr  : int
  var lo   : alog
  var lr   : alog
}.

module H : HOracles = {
  proc h0(x : row * msg * int * row) : cmt = { return St.h0 x.`1 x.`2 x.`3 x.`4; }
  proc h1(x : row * msg * committee * cmt list) : view = { return St.h1 x.`1 x.`2 x.`3 x.`4; }
  proc hc(x : row * row * msg) : rq = { return St.hc x.`1 x.`2 x.`3; }
}.

module O : TOracles = {
  proc o1(i : int, mu : msg) : (int * cmt) option = {
    var r, e, tok, out;
    out <- None;
    if (1 <= i <= nmax /\ !(i \in St.cs)) {
      r <$ dnonce;
      e <$ dnoiser;
      tok <- sign1 St.h0 St.vk i mu r e;
      St.toks.[St.ctr] <- tok;
      out <- Some (St.ctr, tok.`tk_cmt);
      St.ctr <- St.ctr + 1;
    }
    return out;
  }

  proc o2(u : int, T : committee, cs : cmt list) : row option = {
    var out, x, tok;
    out <- None;
    if (u \in St.toks) {
      tok <- oget St.toks.[u];
      x <- sign2 St.h1 St.vk tok T cs;
      if (x <> None) {
        St.toks.[u] <- (oget x).`1;
        St.req.[u] <- (tok.`tk_msg, T, cs);
        St.lo <- ((tok.`tk_msg, T, cs), tok.`tk_i) :: St.lo;
        out <- Some (oget x).`2;
      }
    }
    return out;
  }

  proc o3(u : int, T : committee, cs : cmt list, ws : row list) : vec option = {
    var out, x, tok;
    out <- None;
    if (u \in St.toks) {
      tok <- oget St.toks.[u];
      x <- sign3 St.h0 St.h1 St.hc St.vk (shr St.s St.p tok.`tk_i) tok T cs ws;
      if (x <> None) {
        St.toks.[u] <- (oget x).`1;
        St.lr <- (oget St.req.[u], tok.`tk_i) :: St.lr;
        out <- Some (oget x).`2;
      }
    }
    return out;
  }
}.

module Game (A : Adv) = {
  var mu : msg
  var ok : bool

  proc main() : unit = {
    var e, sg;
    St.h0 <$ dh0;
    St.h1 <$ dh1;
    St.hc <$ dhc;
    St.cs <@ A(H, O).corrupt();
    St.s <$ dsecret;
    e <$ derr;
    St.p <$ dpoly;
    St.vk <- rndt (mulA mA St.s + e);
    St.toks <- empty;
    St.req <- empty;
    St.ctr <- 0;
    St.lo <- [];
    St.lr <- [];
    (mu, sg) <@ A(H, O).forge(St.vk, fun j => if j \in St.cs then shr St.s St.p j else RqVec.Vector.zerov);
    ok <- verify St.hc St.vk mu sg /\ cadm St.cs;
  }
}.

op tokOK (toks : (int, token) fmap) (i : int) (V : request) : bool =
  i \in V.`2 /\
  exists u, u \in toks /\ (oget toks.[u]).`tk_i = i
            /\ (oget toks.[u]).`tk_cmt = nth witness V.`3 (index i V.`2).

pred inv (cs : corrset) (toks : (int, token) fmap) (req : (int, request) fmap)
         (ctr : int) (lo lr : alog) =
  (forall u, u \in toks => 0 <= u < ctr /\ !((oget toks.[u]).`tk_i \in cs))
  /\ (forall V i, (V, i) \in lo => !(i \in cs) /\ tokOK toks i V)
  /\ (forall u, u \in req => u \in toks /\ (oget req.[u], (oget toks.[u]).`tk_i) \in lo)
  /\ (forall e, e \in lr => e \in lo)
  /\ 0 <= ctr.

(* Index preserving updates keep validity *)
lemma tokOK_update (toks : (int, token) fmap) u (t' : token) i V :
  u \in toks => t'.`tk_i = (oget toks.[u]).`tk_i => t'.`tk_cmt = (oget toks.[u]).`tk_cmt =>
  tokOK toks i V => tokOK toks.[u <- t'] i V.
proof.
move=> hu hi hc [] hV [u0] [#] hu0 hi0 hc0; split => //.
exists u0; rewrite mem_set hu0 /= get_setE.
case: (u0 = u) => [heq | hne].
+ by rewrite /= hi hc -heq hi0 hc0.
by rewrite /= hi0 hc0.
qed.

(* The first oracle preserves the invariant *)
lemma o1_inv :
  hoare [O.o1 : inv St.cs St.toks St.req St.ctr St.lo St.lr
                ==> inv St.cs St.toks St.req St.ctr St.lo St.lr].
proof.
proc; sp; if; last by skip.
auto => /> &m htk hlo hreq hlr hctr hi1 hi2 hic r _ e _; split.
+ move=> u; rewrite mem_set get_setE; case: (u = St.ctr{m}) => [-> /= | hne /=].
  - by rewrite /sign1 /=; smt().
  by move=> hu; have := htk u hu; smt().
split.
+ move=> V i /hlo [] hni hok; split => //.
  have [hV [u0] [#] hu0 hi0 hc0] := hok; split => //.
  exists u0; rewrite mem_set hu0 /= get_setE.
  have hne : u0 <> St.ctr{m} by have := htk u0 hu0; smt().
  by rewrite hne /= hi0 hc0.
split.
+ move=> u /hreq [] hu hl; rewrite mem_set hu /= get_setE.
  have hne : u <> St.ctr{m} by have := htk u hu; smt().
  by rewrite hne.
by smt().
qed.

(* The second oracle preserves the invariant *)
lemma o2_inv :
  hoare [O.o2 : inv St.cs St.toks St.req St.ctr St.lo St.lr
                ==> inv St.cs St.toks St.req St.ctr St.lo St.lr].
proof.
proc; wp; skip => &m hinv.
have [htk [hlo [hreq [hlr hctr]]]] := hinv.
case: (u{m} \in St.toks{m}) => hu //=.
have [hx | [y hy]] : sign2 St.h1{m} St.vk{m} (oget St.toks{m}.[u{m}]) T{m} cs{m} = None
                   \/ exists y, sign2 St.h1{m} St.vk{m} (oget St.toks{m}.[u{m}]) T{m} cs{m} = Some y.
+ by case: (sign2 St.h1{m} St.vk{m} (oget St.toks{m}.[u{m}]) T{m} cs{m}) => [| y]; [left | right; exists y].
+ by rewrite hx.
rewrite hy /=.
have [#] hok2 hph hT hdig hw hi hmsg hr he hwb hcm := sign2_some _ _ _ _ _ _ hy.
have [hu1 hhon] := htk u{m} hu.
split.
+ move=> u'; rewrite mem_set get_setE; case: (u' = u{m}) => [-> /= | hne /=].
  - by rewrite hi; smt().
  by move=> hu'; exact (htk u' hu').
split.
+ move=> V i; rewrite in_cons => -[[] -> ->|].
  - split; first by done.
    move: hok2; rewrite /ok2 /own_cmt => [#] _ _ _ hin _ hown.
    split; first by done.
    exists u{m}; rewrite mem_set get_set_sameE /= hi hcm.
    by rewrite hown.
  move=> /hlo [] hni hok; split => //.
  by apply (tokOK_update St.toks{m} u{m} y.`1 i V hu hi hcm hok).
split.
+ move=> u'; rewrite mem_set get_setE; case: (u' = u{m}) => [-> /= | hne /=].
  - by rewrite get_set_sameE /= mem_set /= hi.
  move=> hu'; have [hu'' hl] := hreq u' hu'.
  rewrite mem_set hu'' /=.
  by right; rewrite get_setE hne /=; exact hl.
split; last by done.
by move=> e /hlr he'; rewrite in_cons he'.
qed.

pred reqinv (toks : (int, token) fmap) (req : (int, request) fmap) =
  forall u, u \in toks => (oget toks.[u]).`tk_phase = 2 => u \in req.

(* The third oracle preserves the invariant *)
lemma o3_inv :
  hoare [O.o3 : inv St.cs St.toks St.req St.ctr St.lo St.lr /\ reqinv St.toks St.req
                ==> inv St.cs St.toks St.req St.ctr St.lo St.lr /\ reqinv St.toks St.req].
proof.
proc; wp; skip => &m [hinv hri].
have [htk [hlo [hreq [hlr hctr]]]] := hinv.
case: (u{m} \in St.toks{m}) => hu //=.
pose sk := shr St.s{m} St.p{m} (oget St.toks{m}.[u{m}]).`tk_i.
have [hx | [y hy]] : sign3 St.h0{m} St.h1{m} St.hc{m} St.vk{m} sk (oget St.toks{m}.[u{m}])
                       T{m} cs{m} ws{m} = None
                   \/ exists y, sign3 St.h0{m} St.h1{m} St.hc{m} St.vk{m} sk
                       (oget St.toks{m}.[u{m}]) T{m} cs{m} ws{m} = Some y.
+ by case: (sign3 St.h0{m} St.h1{m} St.hc{m} St.vk{m} sk (oget St.toks{m}.[u{m}])
                  T{m} cs{m} ws{m}) => [| y]; [left | right; exists y].
+ by rewrite /sk in hx; rewrite hx.
rewrite /sk in hy; rewrite hy /=.
have [hok3 [he hz]] := sign3_some _ _ _ _ _ _ _ _ _ _ hy.
have hp2 : (oget St.toks{m}.[u{m}]).`tk_phase = 2 by move: hok3; rewrite /ok3 => [#].
have hrequ := hri u{m} hu hp2.
have [_ hlog] := hreq u{m} hrequ.
have hi' : y.`1.`tk_i = (oget St.toks{m}.[u{m}]).`tk_i by rewrite he /erase.
have hc' : y.`1.`tk_cmt = (oget St.toks{m}.[u{m}]).`tk_cmt by rewrite he /erase.
split; [split | ].
+ move=> u'; rewrite mem_set get_setE; case: (u' = u{m}) => [-> /= | hne /=].
  - by rewrite hi'; exact (htk u{m} hu).
  by move=> hu'; exact (htk u' hu').
+ split.
  - move=> V i /hlo [] hni hok; split => //.
    by apply (tokOK_update St.toks{m} u{m} y.`1 i V hu hi' hc' hok).
  split.
  - move=> u' /hreq [] hu' hl; rewrite mem_set hu' /= get_setE.
    case: (u' = u{m}) => [heq | hne] /=; last by done.
    by rewrite hi' -heq.
  split; last by done.
  move=> e; rewrite in_cons => -[->|]; last by exact hlr.
  by exact hlog.
move=> u'; rewrite mem_set get_setE; case: (u' = u{m}) => [-> /= | hne /=].
+ by rewrite he /erase.
by move=> hu' hp; exact (hri u' hu' hp).
qed.
