require import AllCore Int List Distr DList FMap FSet Real RealExp Finite StdOrder StdBigop.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption.
require import Protocol Notions Privacy Extract FinEnum ChainBase ChainGame ChainCol ChainSim.
require import ChainDead ChainLazy ChainFlag ChainGA.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

(* ---------- the third flag: a response to other first messages with the same digest ----------

   A response whose first messages differ from those of the opened request while the digests
   agree gives two distinct inputs of H1 with the same value (the encoding e1 is injective on well
   formed requests).  The collision finder runs the game with H1 through its oracle. *)

module Lc = {
  var got : bool
  var x1  : h1in
  var x2  : h1in
}.

module HOL3 (H : H1O.QRO_i) : HOr = {
  proc h0 = HOL(H0H.LC).h0
  proc h1(x : h1in) : view = { var y; y <@ H.h(x); return y; }
  proc hc = HOL(H0H.LC).hc
}.

module SOA3 (H : H1O.QRO_i) : SOr = {
  proc h0any = SOA(H0H.LC).h0any

  proc o1 = SOA(H0H.LC).o1

  proc o2(u : int, T : committee, cs : cmt list) : row option = {
    var out, tok, d, s;
    out <- None;
    if (u \in S.toks) {
      tok <- oget S.toks.[u];
      if (ok2 tok T cs) {
        d <@ H.h(e1 S.t tok.`tk_msg T cs);
        s <@ H0H.LC.reveal(u);
        S.toks.[u] <- {| tok with tk_r = s.`1; tk_e = s.`2; tk_wbar = popn s; tk_phase = 2;
                                  tk_T = T; tk_dig = d |};
        S.req.[u] <- (tok.`tk_msg, T, cs);
        S.lo <- ((tok.`tk_msg, T, cs), tok.`tk_i) :: S.lo;
        out <- Some (popn s);
      }
    }
    return out;
  }

  proc o3(u : int, T : committee, cs : cmt list, ws : row list) : vec option = {
    var out, tok, d, k, okk, y, c, z, mkh, mkc, j, v, ys, f;
    out <- None;
    if (u \in S.toks) {
      tok <- oget S.toks.[u];
      if (tok.`tk_phase = 2 /\ T = tok.`tk_T /\ size cs = size T /\ size ws = size T
          /\ nth witness ws (index tok.`tk_i T) = tok.`tk_wbar) {
        d <@ H.h(e1 S.t tok.`tk_msg T cs);
        if (d = tok.`tk_dig) {
          if (!Lc.got /\ cs <> (oget S.req.[u]).`3) {
            Lc.got <- true;
            Lc.x1 <- e1 S.t tok.`tk_msg T cs;
            Lc.x2 <- e1 S.t (oget S.req.[u]).`1 (oget S.req.[u]).`2 (oget S.req.[u]).`3;
          }
          Bd.b3 <- Bd.b3 \/ cs <> (oget S.req.[u]).`3;
          okk <- true;
          k <- 0;
          while (k < size T) {
            y <@ h0any((((S.t, tok.`tk_msg), toidx (nth 0 T k)), nth witness ws k));
            okk <- okk /\ y = nth witness cs k;
            Bd.b1 <- Bd.b1 \/ (!(nth 0 T k \in S.cs) /\ y = nth witness cs k
                               /\ incons S.toks (nth 0 T k) tok.`tk_msg (nth witness cs k)
                                         (nth witness ws k));
            k <- k + 1;
          }
          if (okk) {
            c <- HCO.QRO.fh (liftw (aggw ws), (S.t, tok.`tk_msg));
            ys <- filter (fun j => j <> tok.`tk_i /\ hpair S.cs tok.`tk_i j
                                   /\ !((oget S.req.[u], j) \in S.lr)) T;
            mkh <- RqVec.Vector.zerov;
            mkc <- RqVec.Vector.zerov;
            k <- 0;
            while (k < size T) {
              j <- nth 0 T k;
              if (j <> tok.`tk_i /\ !(ys <> [] /\ j = head 0 ys)) {
                if (hpair S.cs tok.`tk_i j) {
                } else {
                  v <- prf (S.sdc (toidx (if tok.`tk_i < j then tok.`tk_i else j),
                                   toidx (if tok.`tk_i < j then j else tok.`tk_i))) d;
                  mkc <- mkc + (if tok.`tk_i < j then v else - v);
                }
              }
              k <- k + 1;
            }
            f <- (Rq.( * ) c (lam_of T tok.`tk_i)) ** shr S.s S.p tok.`tk_i + tok.`tk_r + mkc;
            if ((oget S.req.[u], tok.`tk_i) \in S.lr) {
              z <- (oget Fz.fz.[(oget S.req.[u], tok.`tk_i)]).`1 + f
                   - (oget Fz.fz.[(oget S.req.[u], tok.`tk_i)]).`2;
            } else {
              if (ys <> []) {
                z <$ dvec;
              } else {
                z <- f + vmap (fun a => (oget Fz.fz.[(oget S.req.[u], a)]).`2
                                        - (oget Fz.fz.[(oget S.req.[u], a)]).`1)
                              (filter (fun a => a <> tok.`tk_i) (honest T S.cs));
              }
              Fz.fz.[(oget S.req.[u], tok.`tk_i)] <- (z, f);
            }
            S.toks.[u] <- erase tok;
            S.lr <- (oget S.req.[u], tok.`tk_i) :: S.lr;
            out <- Some z;
          }
        }
      }
    }
    return out;
  }
}.

module B3c (A : Adv) (H : H1O.QRO_i) = {
  proc main() : h1in * h1in = {
    var mu, sg, sks, sds;
    H0H.QRO.init();
    H0H.LC.sv <- empty;
    H0H.LC.rv <- [];
    H0H.LC.fv <- empty;
    H0H.LC.lft <- true;
    H0H.CQ.n <- 0;
    H0C.QRO.init();
    HCO.QRO.init();
    Lc.got <- false;
    Lc.x1 <- witness;
    Lc.x2 <- witness;
    S.cs <@ A(CntH(HOL3(H)), CntO(SOA3(H))).corrupt();
    S.s <$ dskey;
    S.e <$ dekey;
    S.p <$ dpoly;
    S.t <- rndkey (mulA mA S.s + S.e);
    S.sdc <$ dseedf;
    S.toks <- empty;
    S.req <- empty;
    S.ctr <- 0;
    S.lo <- [];
    S.lr <- [];
    Fz.fz <- empty;
    Bd.b1 <- false;
    Bd.b2 <- false;
    Bd.b3 <- false;
    Cnt.c0 <- 0;
    Cnt.c1 <- 0;
    Cnt.cc <- 0;
    Cnt.cs <- 0;
    sks <- fun j => if j \in S.cs then shr S.s S.p j else RqVec.Vector.zerov;
    sds <- fun (ab : pidx * pidx) =>
             if hpair S.cs (PIdx.val ab.`1) (PIdx.val ab.`2) then witness else S.sdc ab;
    (mu, sg) <@ A(CntH(HOL3(H)), CntO(SOA3(H))).forge(S.t, sks, sds);
    return (Lc.x1, Lc.x2);
  }
}.

(* The opened tokens keep the digest of their request *)
op b3i (toks : (int, token) fmap) (req : (int, request) fmap) (t : row) (fh : h1in -> view) : bool =
  forall u, u \in toks => (oget toks.[u]).`tk_phase = 2 =>
    u \in req /\ (oget req.[u]).`1 = (oget toks.[u]).`tk_msg /\ (oget req.[u]).`2 = (oget toks.[u]).`tk_T
    /\ wfreq (oget req.[u])
    /\ (oget toks.[u]).`tk_dig = fh (e1 t (oget req.[u]).`1 (oget req.[u]).`2 (oget req.[u]).`3).

(* A recorded pair is a collision *)
op colok (got : bool) (x1 x2 : h1in) (fh : h1in -> view) : bool = got => x1 <> x2 /\ fh x1 = fh x2.

section B3.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -Fz, -Bd, -Lc, -H0H.QRO, -H0C.QRO, -H1O.QRO,
                         -HCO.QRO, -H0H.LC, -H0H.CQ, -H1O.CQ}.

declare axiom e1_inj (t t' : row) (V V' : request) :
  wfreq V => wfreq V' => e1 t V.`1 V.`2 V.`3 = e1 t' V'.`1 V'.`2 V'.`3 => t = t' /\ V = V'.

declare axiom A_bnd (H <: HOr {-A, -Cnt}) (O <: SOr {-A, -Cnt}) :
  hoare [A(CntH(H), CntO(O)).forge : Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 ==>
         Cnt.c0 <= qh0 /\ Cnt.c1 <= qh1 /\ Cnt.cc <= qhc /\ Cnt.cs <= qsig].

local lemma o1_b3 :
  hoare [CntO(SOA3(H1O.CQ)).o1 :
    b3i S.toks S.req S.t H1O.QRO.fh /\ colok Lc.got Lc.x1 Lc.x2 H1O.QRO.fh /\ (Bd.b3 => Lc.got) ==>
    b3i S.toks S.req S.t H1O.QRO.fh /\ colok Lc.got Lc.x1 Lc.x2 H1O.QRO.fh /\ (Bd.b3 => Lc.got)].
proof.
proc; inline SOA3(H1O.CQ).o1; sp; if; last by auto.
inline *; sp; if; (sp; if; auto => />; rewrite /b3i => *; smt(mem_set get_setE)) || 
  (auto => />; rewrite /b3i => *; smt(mem_set get_setE)).
qed.

local lemma o2_b3 :
  hoare [CntO(SOA3(H1O.CQ)).o2 :
    b3i S.toks S.req S.t H1O.QRO.fh /\ colok Lc.got Lc.x1 Lc.x2 H1O.QRO.fh /\ (Bd.b3 => Lc.got) ==>
    b3i S.toks S.req S.t H1O.QRO.fh /\ colok Lc.got Lc.x1 Lc.x2 H1O.QRO.fh /\ (Bd.b3 => Lc.got)].
proof.
proc; inline SOA3(H1O.CQ).o2; sp; if; last by auto.
sp; if; last by auto.
by inline *; sp; if; auto => />; rewrite /b3i /wfreq /wf_committee => *; smt(mem_set get_setE).
qed.

local lemma o3_b3 :
  hoare [CntO(SOA3(H1O.CQ)).o3 :
    b3i S.toks S.req S.t H1O.QRO.fh /\ colok Lc.got Lc.x1 Lc.x2 H1O.QRO.fh /\ (Bd.b3 => Lc.got) ==>
    b3i S.toks S.req S.t H1O.QRO.fh /\ colok Lc.got Lc.x1 Lc.x2 H1O.QRO.fh /\ (Bd.b3 => Lc.got)].
proof.
proc; inline SOA3(H1O.CQ).o3; sp; if; last by auto.
sp; if; last by auto.
inline H1O.CQ.h; sp; if; last by auto.
seq 4 : (b3i S.toks S.req S.t H1O.QRO.fh /\ colok Lc.got Lc.x1 Lc.x2 H1O.QRO.fh /\ (Bd.b3 => Lc.got)
         /\ u0 \in S.toks /\ tok = oget S.toks.[u0]).
+ auto => /> &h hb3 hcol hgot hu hph hcs hws hnth hd; split.
  - move=> hng hne; split; last first.
    + by have := hb3 u{h} hu hph; smt().
    apply/negP => heq.
    have [hr [h1 [h2 [hw _]]]] := hb3 u{h} hu hph.
    have := e1_inj S.t{h} S.t{h}
              ((oget S.toks{h}.[u{h}]).`tk_msg, (oget S.toks{h}.[u{h}]).`tk_T, cs{h})
              (oget S.req{h}.[u{h}]) _ hw _.
    * by move: hw; rewrite /wfreq /= h2; smt().
    * by rewrite /= heq.
    by move=> [_ heqV]; apply hne; rewrite -heqV.
  by move=> hng; smt().
seq 1 : (b3i S.toks S.req S.t H1O.QRO.fh /\ colok Lc.got Lc.x1 Lc.x2 H1O.QRO.fh /\ (Bd.b3 => Lc.got)
         /\ u0 \in S.toks /\ tok = oget S.toks.[u0]).
+ while (b3i S.toks S.req S.t H1O.QRO.fh /\ colok Lc.got Lc.x1 Lc.x2 H1O.QRO.fh /\ (Bd.b3 => Lc.got)
         /\ u0 \in S.toks /\ tok = oget S.toks.[u0]); last by auto.
  wp; call (_ : true); last by auto.
  by sp; if; [auto | inline *; sp; if; [sp; if; auto | auto]].
if; last by auto.
seq 6 : (b3i S.toks S.req S.t H1O.QRO.fh /\ colok Lc.got Lc.x1 Lc.x2 H1O.QRO.fh /\ (Bd.b3 => Lc.got)
         /\ u0 \in S.toks /\ tok = oget S.toks.[u0]).
+ by while (b3i S.toks S.req S.t H1O.QRO.fh /\ colok Lc.got Lc.x1 Lc.x2 H1O.QRO.fh /\ (Bd.b3 => Lc.got)
            /\ u0 \in S.toks /\ tok = oget S.toks.[u0]); auto.
by sp; if; [auto | if; auto] => />; rewrite /b3i => *; smt(mem_set get_setE).
qed.

local lemma h0_b3 :
  hoare [CntH(HOL3(H1O.CQ)).h0 :
    b3i S.toks S.req S.t H1O.QRO.fh /\ colok Lc.got Lc.x1 Lc.x2 H1O.QRO.fh /\ (Bd.b3 => Lc.got) ==>
    b3i S.toks S.req S.t H1O.QRO.fh /\ colok Lc.got Lc.x1 Lc.x2 H1O.QRO.fh /\ (Bd.b3 => Lc.got)].
proof. by proc; inline *; sp; if; [auto | sp; if; [sp; if; auto | auto]]. qed.

local lemma h1_b3 :
  hoare [CntH(HOL3(H1O.CQ)).h1 :
    b3i S.toks S.req S.t H1O.QRO.fh /\ colok Lc.got Lc.x1 Lc.x2 H1O.QRO.fh /\ (Bd.b3 => Lc.got) ==>
    b3i S.toks S.req S.t H1O.QRO.fh /\ colok Lc.got Lc.x1 Lc.x2 H1O.QRO.fh /\ (Bd.b3 => Lc.got)].
proof. by proc; inline *; auto. qed.

local lemma hc_b3 :
  hoare [CntH(HOL3(H1O.CQ)).hc :
    b3i S.toks S.req S.t H1O.QRO.fh /\ colok Lc.got Lc.x1 Lc.x2 H1O.QRO.fh /\ (Bd.b3 => Lc.got) ==>
    b3i S.toks S.req S.t H1O.QRO.fh /\ colok Lc.got Lc.x1 Lc.x2 H1O.QRO.fh /\ (Bd.b3 => Lc.got)].
proof. by proc; inline *; auto. qed.

local equiv o1_e3 :
  CntO(SOA(H0H.LC)).o1 ~ CntO(SOA3(H1O.CQ)).o1 :
  ={i, mu} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO} /\ b3i S.toks{2} S.req{2} S.t{2} H1O.QRO.fh{2} /\ colok Lc.got{2} Lc.x1{2} Lc.x2{2} H1O.QRO.fh{2}
    /\ (Bd.b3{2} => Lc.got{2}) ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO} /\ b3i S.toks{2} S.req{2} S.t{2} H1O.QRO.fh{2} /\ colok Lc.got{2} Lc.x1{2} Lc.x2{2} H1O.QRO.fh{2}
    /\ (Bd.b3{2} => Lc.got{2}).
proof.
conseq (_ : ={i, mu} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO}) _ o1_b3 => //.
by proc; inline *; sim.
qed.

local equiv o2_e3 :
  CntO(SOA(H0H.LC)).o2 ~ CntO(SOA3(H1O.CQ)).o2 :
  ={u, T, cs} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO} /\ b3i S.toks{2} S.req{2} S.t{2} H1O.QRO.fh{2} /\ colok Lc.got{2} Lc.x1{2} Lc.x2{2} H1O.QRO.fh{2}
    /\ (Bd.b3{2} => Lc.got{2}) ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO} /\ b3i S.toks{2} S.req{2} S.t{2} H1O.QRO.fh{2} /\ colok Lc.got{2} Lc.x1{2} Lc.x2{2} H1O.QRO.fh{2}
    /\ (Bd.b3{2} => Lc.got{2}).
proof.
conseq (_ : ={u, T, cs} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO}) _ o2_b3 => //.
proc; inline SOA(H0H.LC).o2 SOA3(H1O.CQ).o2; sp; if => //; last by auto.
sp; if => //; last by auto.
inline H1O.CQ.h; wp; call (_ : ={glob H0H.LC}); first by sim.
by auto.
qed.

local equiv o3_e3 :
  CntO(SOA(H0H.LC)).o3 ~ CntO(SOA3(H1O.CQ)).o3 :
  ={u, T, cs, ws} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO} /\ b3i S.toks{2} S.req{2} S.t{2} H1O.QRO.fh{2} /\ colok Lc.got{2} Lc.x1{2} Lc.x2{2} H1O.QRO.fh{2}
    /\ (Bd.b3{2} => Lc.got{2}) ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO} /\ b3i S.toks{2} S.req{2} S.t{2} H1O.QRO.fh{2} /\ colok Lc.got{2} Lc.x1{2} Lc.x2{2} H1O.QRO.fh{2}
    /\ (Bd.b3{2} => Lc.got{2}).
proof.
conseq (_ : ={u, T, cs, ws} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO}) _ o3_b3 => //.
proc; inline SOA(H0H.LC).o3 SOA3(H1O.CQ).o3; sp; if => //; last by auto.
sp; if => //; last by auto.
inline H1O.CQ.h; sp; if; [by move=> &1 &2 /> | | by auto].
seq 1 2 : (={u0, T0, cs0, ws0, tok, d, out} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO}); first by auto.
by sim.
qed.

local equiv h0_e3 :
  CntH(HOL(H0H.LC)).h0 ~ CntH(HOL3(H1O.CQ)).h0 :
  ={x} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO} /\ b3i S.toks{2} S.req{2} S.t{2} H1O.QRO.fh{2} /\ colok Lc.got{2} Lc.x1{2} Lc.x2{2} H1O.QRO.fh{2}
    /\ (Bd.b3{2} => Lc.got{2}) ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO} /\ b3i S.toks{2} S.req{2} S.t{2} H1O.QRO.fh{2} /\ colok Lc.got{2} Lc.x1{2} Lc.x2{2} H1O.QRO.fh{2}
    /\ (Bd.b3{2} => Lc.got{2}).
proof.
conseq (_ : ={x} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO}) _ h0_b3 => //.
by proc; inline *; sim.
qed.

local equiv h1_e3 :
  CntH(HOL(H0H.LC)).h1 ~ CntH(HOL3(H1O.CQ)).h1 :
  ={x} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO} /\ b3i S.toks{2} S.req{2} S.t{2} H1O.QRO.fh{2} /\ colok Lc.got{2} Lc.x1{2} Lc.x2{2} H1O.QRO.fh{2}
    /\ (Bd.b3{2} => Lc.got{2}) ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO} /\ b3i S.toks{2} S.req{2} S.t{2} H1O.QRO.fh{2} /\ colok Lc.got{2} Lc.x1{2} Lc.x2{2} H1O.QRO.fh{2}
    /\ (Bd.b3{2} => Lc.got{2}).
proof.
conseq (_ : ={x} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO}) _ h1_b3 => //.
by proc; inline *; sim.
qed.

local equiv hc_e3 :
  CntH(HOL(H0H.LC)).hc ~ CntH(HOL3(H1O.CQ)).hc :
  ={x} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO} /\ b3i S.toks{2} S.req{2} S.t{2} H1O.QRO.fh{2} /\ colok Lc.got{2} Lc.x1{2} Lc.x2{2} H1O.QRO.fh{2}
    /\ (Bd.b3{2} => Lc.got{2}) ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO} /\ b3i S.toks{2} S.req{2} S.t{2} H1O.QRO.fh{2} /\ colok Lc.got{2} Lc.x1{2} Lc.x2{2} H1O.QRO.fh{2}
    /\ (Bd.b3{2} => Lc.got{2}).
proof.
conseq (_ : ={x} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO}) _ hc_b3 => //.
by proc; inline *; sim.
qed.

(* A raised third flag gives an H1 collision *)
lemma gaf_col3 &m : Pr[GAf(A).main() @ &m : Bd.b3] <= Pr[H1O.Col(B3c(A)).main() @ &m : res].
proof.
byequiv => //; proc.
inline B3c(A, H1O.CQ).main.
wp.
call (_ : ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, H1O.QRO.fh, glob HCO.QRO} /\ b3i S.toks{2} S.req{2} S.t{2} H1O.QRO.fh{2} /\ colok Lc.got{2} Lc.x1{2} Lc.x2{2} H1O.QRO.fh{2}
    /\ (Bd.b3{2} => Lc.got{2})).
+ exact o1_e3.
+ exact o2_e3.
+ exact o3_e3.
+ exact h0_e3.
+ exact h1_e3.
+ exact hc_e3.
auto; call (_ : true).
swap{1} 8 -7.
inline *; auto => /> *.
split; first by rewrite /b3i => u; rewrite mem_empty.
by move=> _ _ got x1 x2 req toks b3 _ hcol hgot hb3; apply hcol; apply hgot.
qed.

(* The collision finder asks H1 at most qh1 + qsig times *)
local lemma forge_cq :
  hoare [A(CntH(HOL3(H1O.CQ)), CntO(SOA3(H1O.CQ))).forge :
    Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 /\ H1O.CQ.n = 0 ==> H1O.CQ.n <= qh1 + qsig].
proof.
conseq (A_bnd (HOL3(H1O.CQ)) (SOA3(H1O.CQ)))
       (_ : H1O.CQ.n <= Cnt.c1 + Cnt.cs ==> H1O.CQ.n <= Cnt.c1 + Cnt.cs) => //; first smt().
proc (H1O.CQ.n <= Cnt.c1 + Cnt.cs) => //.
+ proc; inline SOA3(H1O.CQ).o1; sp; if; last by auto => /> /#.
  by inline *; sp; if; sp; if; auto => /> /#.
+ proc; inline SOA3(H1O.CQ).o2; sp; if; last by auto => /> /#.
  sp; if; last by auto => /> /#.
  by inline *; sp; if; auto => /> /#.
+ proc; inline SOA3(H1O.CQ).o3; sp; if; last by auto => /> /#.
  sp; if; last by auto => /> /#.
  inline H1O.CQ.h; sp; if; last by auto => /> /#.
  seq 4 : (H1O.CQ.n <= Cnt.c1 + Cnt.cs); first by auto => /> /#.
  seq 1 : (H1O.CQ.n <= Cnt.c1 + Cnt.cs).
  + while (H1O.CQ.n <= Cnt.c1 + Cnt.cs); last by auto.
    wp; call (_ : true); last by auto.
    by sp; if; [auto | inline *; sp; if; [sp; if; auto | auto]].
  if; last by auto.
  seq 6 : (H1O.CQ.n <= Cnt.c1 + Cnt.cs); first by while (H1O.CQ.n <= Cnt.c1 + Cnt.cs); auto.
  by sp; if; [auto | if; auto].
+ by proc; inline *; sp; if; [auto | sp; if; [sp; if; auto | auto]].
+ by proc; inline *; auto => /> /#.
+ by proc; inline *; auto.
qed.

local lemma b3c_cnt : hoare [B3c(A, H1O.CQ).main : H1O.CQ.n = 0 ==> H1O.CQ.n <= qh1 + qsig].
proof.
proc; call forge_cq.
by inline *; auto; call (_ : true); auto.
qed.

(* A response to other first messages with the same digest is unlikely *)
lemma ga_b3 &m :
  Pr[H0H.LCG(BA(A)).main(true) @ &m : Bd.b3] <= 27%r * (qh1 + qsig + 2)%r ^ 3 * p_max dview.
proof.
have -> := ga_gaf A &m (fun _ _ _ _ b3 _ _ _ _ => b3).
apply (StdOrder.RealOrder.ler_trans _ _ _ (gaf_col3 &m)).
exact (H1O.pr_col (B3c(A)) &m (qh1 + qsig) b3c_cnt).
qed.

end section B3.
