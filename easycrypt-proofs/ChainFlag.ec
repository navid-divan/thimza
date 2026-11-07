require import AllCore Int List Distr DList FMap FSet Real RealExp Finite StdOrder.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption.
require import Protocol Notions Privacy Extract FinEnum ChainBase ChainGame ChainCol ChainSim ChainDead ChainLazy.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

(* The flags of the opening aborts of the games G2 and G5 of the paper *)
module Bd = {
  var b1 : bool
  var b2 : bool
  var b3 : bool
}.

(* The token u of party j holds the first message c *)
op cmtok (toks : (int, token) fmap) (j : int) (c : cmt) (u : int) : bool =
  u \in toks /\ (oget toks.[u]).`tk_i = j /\ (oget toks.[u]).`tk_cmt = c.

(* An accepted entry that disagrees with the token holding its first message *)
op incons (toks : (int, token) fmap) (j : int) (mu : msg) (c : cmt) (w : row) : bool =
  exists u, cmtok toks j c u
    /\ ((oget toks.[u]).`tk_phase = 1 \/ (oget toks.[u]).`tk_msg <> mu
        \/ (oget toks.[u]).`tk_wbar <> w).

(* A first message already held by a token *)
op dupc (toks : (int, token) fmap) (c : cmt) : bool =
  exists u, u \in toks /\ (oget toks.[u]).`tk_cmt = c.

(* A first message that already occurs in a request with a response *)
op seenc (lr : alog) (c : cmt) : bool =
  exists (V : request) (a : int), (V, a) \in lr /\ c \in V.`3.

module SOA (O : H0H.LC_i) : SOr = {
  proc h0any = SOL(O).h0any

  proc o1(i : int, mu : msg) : (int * cmt) option = {
    var c, out;
    out <- None;
    if (1 <= i <= nmax /\ !(i \in S.cs)) {
      c <@ O.commit(S.ctr, ((S.t, mu), toidx i));
      Bd.b2 <- Bd.b2 \/ dupc S.toks c \/ seenc S.lr c;
      S.toks.[S.ctr] <- {| tk_i = i; tk_msg = mu; tk_r = witness; tk_e = witness; tk_wbar = witness;
                           tk_cmt = c; tk_phase = 1; tk_T = []; tk_dig = witness |};
      out <- Some (S.ctr, c);
      S.ctr <- S.ctr + 1;
    }
    return out;
  }

  proc o2 = SOL(O).o2

  proc o3(u : int, T : committee, cs : cmt list, ws : row list) : vec option = {
    var out, tok, d, k, okk, y, c, z, mkh, mkc, j, v, ys, f;
    out <- None;
    if (u \in S.toks) {
      tok <- oget S.toks.[u];
      if (tok.`tk_phase = 2 /\ T = tok.`tk_T /\ size cs = size T /\ size ws = size T
          /\ nth witness ws (index tok.`tk_i T) = tok.`tk_wbar) {
        d <- H1O.QRO.fh (e1 S.t tok.`tk_msg T cs);
        if (d = tok.`tk_dig) {
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

module GameA (A : Adv) (O : H0H.LC_i) = {
  proc run() : bool = {
    var mu, sg, ok, sks, sds;
    S.cs <@ A(CntH(HOL(O)), CntO(SOA(O))).corrupt();
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
    (mu, sg) <@ A(CntH(HOL(O)), CntO(SOA(O))).forge(S.t, sks, sds);
    ok <- verify (hcof HCO.QRO.fh) S.t mu sg /\ admc S.cs;
    return win4 S.cs S.lo mu ok;
  }
}.

module BA (A : Adv) (O : H0H.LC_i) = {
  proc main() : bool = {
    var b;
    H0C.QRO.init();
    H1O.QRO.init();
    HCO.QRO.init();
    b <@ GameA(A, O).run();
    return b;
  }
}.

section FlagHop.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -Fz, -Bd, -H0H.QRO, -H0C.QRO, -H1O.QRO,
                         -HCO.QRO, -H0H.LC, -H0H.CQ}.

(* The flags do not change the lazy game *)
lemma gl_ga &m :
  Pr[H0H.LCG(BL(A)).main(true) @ &m : res] = Pr[H0H.LCG(BA(A)).main(true) @ &m : res].
proof.
byequiv => //; proc.
inline BL(A, H0H.LC).main BA(A, H0H.LC).main GameL(A, H0H.LC).run GameA(A, H0H.LC).run.
wp.
call (_ : ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt,
            glob Fz, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H1O.QRO,
            glob HCO.QRO}).
+ by proc; inline *; sim.
+ by proc; inline *; sim.
+ by proc; inline *; sim.
+ by proc; inline *; sim.
+ by proc; inline *; sim.
+ by proc; inline *; sim.
by inline *; auto; call (_ : true); auto.
qed.

(* The winning event splits on the opening flags *)
lemma ga_split &m :
  Pr[H0H.LCG(BA(A)).main(true) @ &m : res]
  <= Pr[H0H.LCG(BA(A)).main(true) @ &m : res /\ !Bd.b1 /\ !Bd.b2 /\ !Bd.b3]
     + Pr[H0H.LCG(BA(A)).main(true) @ &m : Bd.b1]
     + Pr[H0H.LCG(BA(A)).main(true) @ &m : Bd.b2]
     + Pr[H0H.LCG(BA(A)).main(true) @ &m : Bd.b3].
proof.
have h1 : Pr[H0H.LCG(BA(A)).main(true) @ &m : res]
       <= Pr[H0H.LCG(BA(A)).main(true) @ &m : res /\ !Bd.b1 /\ !Bd.b2 /\ !Bd.b3]
          + Pr[H0H.LCG(BA(A)).main(true) @ &m : Bd.b1 \/ Bd.b2 \/ Bd.b3].
+ rewrite Pr[mu_split (Bd.b1 \/ Bd.b2 \/ Bd.b3)].
  have : Pr[H0H.LCG(BA(A)).main(true) @ &m : res /\ (Bd.b1 \/ Bd.b2 \/ Bd.b3)]
      <= Pr[H0H.LCG(BA(A)).main(true) @ &m : Bd.b1 \/ Bd.b2 \/ Bd.b3] by rewrite Pr[mu_sub].
  have -> : Pr[H0H.LCG(BA(A)).main(true) @ &m : res /\ !(Bd.b1 \/ Bd.b2 \/ Bd.b3)]
          = Pr[H0H.LCG(BA(A)).main(true) @ &m : res /\ !Bd.b1 /\ !Bd.b2 /\ !Bd.b3].
  - by rewrite Pr[mu_eq] => /#.
  smt().
have h2 : Pr[H0H.LCG(BA(A)).main(true) @ &m : Bd.b1 \/ Bd.b2 \/ Bd.b3]
       <= Pr[H0H.LCG(BA(A)).main(true) @ &m : Bd.b1]
          + Pr[H0H.LCG(BA(A)).main(true) @ &m : Bd.b2 \/ Bd.b3].
+ by rewrite Pr[mu_or]; smt(mu_bounded).
have h3 : Pr[H0H.LCG(BA(A)).main(true) @ &m : Bd.b2 \/ Bd.b3]
       <= Pr[H0H.LCG(BA(A)).main(true) @ &m : Bd.b2]
          + Pr[H0H.LCG(BA(A)).main(true) @ &m : Bd.b3].
+ by rewrite Pr[mu_or]; smt(mu_bounded).
smt().
qed.

end section FlagHop.
