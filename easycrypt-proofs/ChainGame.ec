require import AllCore Int List Distr DList FMap FSet Real RealExp Finite.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption.
require import Protocol Notions Privacy Extract FinEnum ChainBase.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

module type PRFO = { proc f(i : int, j : int, vw : view) : vec }.

module MPR : PRFO = {
  var k : pidx * pidx -> seed

  proc init() : unit = { k <$ dseedf; }

  proc f(i : int, j : int, vw : view) : vec = { return prf (k (toidx i, toidx j)) vw; }
}.

module MPI : PRFO = {
  var m : ((pidx * pidx) * view, vec) fmap

  proc init() : unit = { m <- empty; }

  proc f(i : int, j : int, vw : view) : vec = {
    var v;
    if (((toidx i, toidx j), vw) \notin m) { v <$ dvec; m.[((toidx i, toidx j), vw)] <- v; }
    return oget m.[((toidx i, toidx j), vw)];
  }
}.

module type MPRFAdv (O : PRFO) = { proc main() : bool }.

module MPRFG (B : MPRFAdv) = {
  proc real() : bool = { var b; MPR.init(); b <@ B(MPR).main(); return b; }
  proc ideal() : bool = { var b; MPI.init(); b <@ B(MPI).main(); return b; }
}.

module Lg = {
  var l0 : (h0in * cmt) list
  var l1 : (h1in * view) list
}.

op hascol ['a 'b] (l : ('a * 'b) list) : bool =
  exists x x' y, (x, y) \in l /\ (x', y) \in l /\ x <> x'.

module HOF (H0h : H0H.QRO_i) (H1 : H1O.QRO_i) : HOr = {
  proc h0(x : h0in) : cmt = {
    var y;
    if (PIdx.val x.`1.`2 \in S.cs) { y <- H0C.QRO.fh x; } else { y <@ H0h.h(x); }
    return y;
  }
  proc h1(x : h1in) : view = { var y; y <@ H1.h(x); return y; }
  proc hc(x : hcin) : rq = { return HCO.QRO.fh x; }
}.

module SOF (P : PRFO) (H0h : H0H.QRO_i) (H1 : H1O.QRO_i) : SOr = {
  proc h0hon(x : h0in) : cmt = {
    var y;
    y <@ H0h.h(x);
    Lg.l0 <- (x, y) :: Lg.l0;
    return y;
  }

  proc h0any(x : h0in) : cmt = {
    var y;
    if (PIdx.val x.`1.`2 \in S.cs) { y <- H0C.QRO.fh x; } else { y <@ h0hon(x); }
    return y;
  }

  proc h1hon(x : h1in) : view = {
    var y;
    y <@ H1.h(x);
    Lg.l1 <- (x, y) :: Lg.l1;
    return y;
  }

  proc o1(i : int, mu : msg) : (int * cmt) option = {
    var nn, w, c, out;
    out <- None;
    if (1 <= i <= nmax /\ !(i \in S.cs)) {
      nn <$ dnonce `*` dnoiser;
      w <- rndc (commit nn.`1 nn.`2);
      c <@ h0hon((((S.t, mu), toidx i), w));
      S.toks.[S.ctr] <- {| tk_i = i; tk_msg = mu; tk_r = nn.`1; tk_e = nn.`2; tk_wbar = w;
                           tk_cmt = c; tk_phase = 1; tk_T = []; tk_dig = witness |};
      out <- Some (S.ctr, c);
      S.ctr <- S.ctr + 1;
    }
    return out;
  }

  proc o2(u : int, T : committee, cs : cmt list) : row option = {
    var out, tok, d;
    out <- None;
    if (u \in S.toks) {
      tok <- oget S.toks.[u];
      if (ok2 tok T cs) {
        d <@ h1hon(e1 S.t tok.`tk_msg T cs);
        S.toks.[u] <- {| tok with tk_phase = 2; tk_T = T; tk_dig = d |};
        S.req.[u] <- (tok.`tk_msg, T, cs);
        S.lo <- ((tok.`tk_msg, T, cs), tok.`tk_i) :: S.lo;
        out <- Some tok.`tk_wbar;
      }
    }
    return out;
  }

  proc o3(u : int, T : committee, cs : cmt list, ws : row list) : vec option = {
    var out, tok, d, k, okk, y, c, z, mkh, mkc, j, v, ys;
    out <- None;
    if (u \in S.toks) {
      tok <- oget S.toks.[u];
      if (tok.`tk_phase = 2 /\ T = tok.`tk_T /\ size cs = size T /\ size ws = size T
          /\ nth witness ws (index tok.`tk_i T) = tok.`tk_wbar) {
        d <@ h1hon(e1 S.t tok.`tk_msg T cs);
        if (d = tok.`tk_dig) {
          okk <- true;
          k <- 0;
          while (k < size T) {
            y <@ h0any((((S.t, tok.`tk_msg), toidx (nth 0 T k)), nth witness ws k));
            okk <- okk /\ y = nth witness cs k;
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
                  v <@ P.f(if tok.`tk_i < j then tok.`tk_i else j,
                           if tok.`tk_i < j then j else tok.`tk_i, d);
                  mkh <- mkh + (if tok.`tk_i < j then v else - v);
                } else {
                  v <- prf (S.sdc (toidx (if tok.`tk_i < j then tok.`tk_i else j),
                                   toidx (if tok.`tk_i < j then j else tok.`tk_i))) d;
                  mkc <- mkc + (if tok.`tk_i < j then v else - v);
                }
              }
              k <- k + 1;
            }
            if (ys <> []) {
              j <- head 0 ys;
              v <@ P.f(if tok.`tk_i < j then tok.`tk_i else j,
                       if tok.`tk_i < j then j else tok.`tk_i, d);
              mkh <- mkh + (if tok.`tk_i < j then v else - v);
            }
            z <- (Rq.( * ) c (lam_of T tok.`tk_i)) ** shr S.s S.p tok.`tk_i + tok.`tk_r + mkc + mkh;
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

module GameF (A : Adv) (P : PRFO) (H0h : H0H.QRO_i) (H1 : H1O.QRO_i) = {
  proc run() : bool = {
    var mu, sg, ok, sks, sds;
    S.cs <@ A(CntH(HOF(H0h, H1)), CntO(SOF(P, H0h, H1))).corrupt();
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
    Lg.l0 <- [];
    Lg.l1 <- [];
    Cnt.c0 <- 0;
    Cnt.c1 <- 0;
    Cnt.cc <- 0;
    Cnt.cs <- 0;
    sks <- fun j => if j \in S.cs then shr S.s S.p j else RqVec.Vector.zerov;
    sds <- fun (ab : pidx * pidx) =>
             if hpair S.cs (PIdx.val ab.`1) (PIdx.val ab.`2) then witness else S.sdc ab;
    (mu, sg) <@ A(CntH(HOF(H0h, H1)), CntO(SOF(P, H0h, H1))).forge(S.t, sks, sds);
    ok <- verify (hcof HCO.QRO.fh) S.t mu sg /\ admc S.cs;
    return win4 S.cs S.lo mu ok;
  }
}.

module G0 (A : Adv) = {
  proc main() : bool = {
    var b;
    MPR.init();
    H0H.QRO.init();
    H0C.QRO.init();
    H1O.QRO.init();
    HCO.QRO.init();
    b <@ GameF(A, MPR, H0H.QRO, H1O.QRO).run();
    return b;
  }
}.

module G1 (A : Adv) = {
  proc main() : bool = {
    var b;
    MPI.init();
    H0H.QRO.init();
    H0C.QRO.init();
    H1O.QRO.init();
    HCO.QRO.init();
    b <@ GameF(A, MPI, H0H.QRO, H1O.QRO).run();
    return b;
  }
}.

module B1 (A : Adv) (O : PRFO) = {
  proc main() : bool = {
    var b;
    H0H.QRO.init();
    H0C.QRO.init();
    H1O.QRO.init();
    HCO.QRO.init();
    b <@ GameF(A, O, H0H.QRO, H1O.QRO).run();
    return b;
  }
}.

section PRFHop.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -H0H.QRO, -H0C.QRO, -H1O.QRO, -HCO.QRO}.

(* The real game is the real PRF experiment *)
lemma g0_real &m : Pr[G0(A).main() @ &m : res] = Pr[MPRFG(B1(A)).real() @ &m : res].
proof. by byequiv => //; proc; inline *; sim. qed.

(* The first game is the ideal PRF experiment *)
lemma g1_ideal &m : Pr[G1(A).main() @ &m : res] = Pr[MPRFG(B1(A)).ideal() @ &m : res].
proof. by byequiv => //; proc; inline *; sim. qed.

(* Random pair masks cost the PRF advantage *)
lemma hop_prf &m :
  `|Pr[G0(A).main() @ &m : res] - Pr[G1(A).main() @ &m : res]|
  = `|Pr[MPRFG(B1(A)).real() @ &m : res] - Pr[MPRFG(B1(A)).ideal() @ &m : res]|.
proof. by rewrite g0_real g1_ideal. qed.

end section PRFHop.
