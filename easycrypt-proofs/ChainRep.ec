require import AllCore Int List Distr DList FMap FSet Real RealExp Finite StdOrder.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption.
require import Protocol Notions Privacy Extract FinEnum ChainBase ChainGame ChainCol ChainSim.
require import ChainDead ChainLazy ChainFlag ChainExt.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

(* The nonce distribution of a token *)
op dnp : (vec * row) distr = dnonce `*` dnoiser.

(* The bound of the regularity lemma for an aggregate commitment *)
op pw2 : real.

(* The token of party j that opened the request V *)
op tokof (toks : (int, token) fmap) (req : (int, request) fmap) (V : request) (j : int) : int =
  choiceb (fun u => u \in toks /\ req.[u] = Some V /\ (oget toks.[u]).`tk_i = j) 0.

(* The truncated commitment with which the honest party j opened V *)
op hwbar (toks : (int, token) fmap) (req : (int, request) fmap) (V : request) (j : int) : row =
  (oget toks.[tokof toks req V j]).`tk_wbar.

(* The extracted opening of the corrupt entry j of V *)
op xwbar (xs : h0in option list) (ix : (request * int, int) fmap) (V : request) (j : int) : row =
  odflt witness (omap snd (nth None xs (oget ix.[(V, j)]))).

(* The openings of a complete request *)
op wsV (toks : (int, token) fmap) (req : (int, request) fmap) (C : corrset)
       (xs : h0in option list) (ix : (request * int, int) fmap) (V : request) : row list =
  map (fun j => if j \in C then xwbar xs ix V j else hwbar toks req V j) V.`2.

(* The challenge point of a request with the given openings *)
op xpt (t : row) (mu : msg) (ws : row list) : hcin = (liftw (aggw ws), (t, mu)).

(* A fresh nonce with the challenge point it fixes at position p *)
op dpt (t : row) (mu : msg) (ws : row list) (p : int) : (hcin * (vec * row)) distr =
  dmap dnp (fun s => (xpt t mu (put ws p (popn s)), s)).

(* The reprogramming records: reprogrammings so far, programmed points, the flags of a point
   programmed twice and of more completions than the budget, and the last opener of each
   complete request *)
module Rx = {
  var nr  : int
  var pts : hcin list
  var bP  : bool
  var bC  : bool
  var lop : (request, int) fmap
}.

module HOR (H : HCO.QRO_i) : HOr = {
  proc h0 = HOE(H0C.ER).h0
  proc h1(x : h1in) : view = { return H1O.QRO.fh x; }
  proc hc(x : hcin) : rq = { var y; y <@ H.h(x); return y; }
}.

module SOR (H : HCO.QRO_i) (R : HCO.Repro_i) : SOr = {
  proc subm(V : request) : unit = {
    var k;
    Ex.dn <- V :: Ex.dn;
    k <- 0;
    while (k < size V.`2) {
      if (nth 0 V.`2 k \in S.cs) {
        Ex.ix.[(V, nth 0 V.`2 k)] <- Ex.n;
        H0C.ER.submit(nth witness V.`3 k);
        Ex.n <- Ex.n + 1;
      }
      k <- k + 1;
    }
  }

  proc o1 = SOA(H0H.LC).o1

  proc o2(u : int, T : committee, cs : cmt list) : row option = {
    var out, tok, d, s, a, vr;
    out <- None;
    if (u \in S.toks) {
      tok <- oget S.toks.[u];
      if (ok2 tok T cs) {
        d <- H1O.QRO.fh (e1 S.t tok.`tk_msg T cs);
        vr <- (tok.`tk_msg, T, cs);
        S.req.[u] <- vr;
        S.lo <- (vr, tok.`tk_i) :: S.lo;
        if (complete vr S.cs S.lo /\ !(vr \in Ex.dn)) {
          subm(vr);
          if (Rx.nr < qsig) {
            a <@ R.reprog(dpt S.t vr.`1 (wsV S.toks S.req S.cs H0C.ER.xs Ex.ix vr)
                              (index tok.`tk_i T));
            Rx.bP <- Rx.bP \/ a.`1 \in Rx.pts;
            Rx.pts <- a.`1 :: Rx.pts;
            Rx.nr <- Rx.nr + 1;
            s <- a.`2;
          } else {
            Rx.bC <- true;
            s <$ dnp;
          }
          if (u \notin H0H.LC.sv) { H0H.LC.sv.[u] <- s; }
          s <- oget H0H.LC.sv.[u];
          if (!(u \in H0H.LC.rv)) { H0H.LC.rv <- u :: H0H.LC.rv; }
          Rx.lop.[vr] <- u;
        } else {
          s <@ H0H.LC.reveal(u);
        }
        S.toks.[u] <- {| tok with tk_r = s.`1; tk_e = s.`2; tk_wbar = popn s; tk_phase = 2;
                                  tk_T = T; tk_dig = d |};
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
        d <- H1O.QRO.fh (e1 S.t tok.`tk_msg T cs);
        if (d = tok.`tk_dig) {
          Bd.b3 <- Bd.b3 \/ cs <> (oget S.req.[u]).`3;
          Ex.cur <- oget S.req.[u];
          okk <- true;
          k <- 0;
          while (k < size T) {
            y <@ SOE(H0C.ER).chk((((S.t, tok.`tk_msg), toidx (nth 0 T k)), nth witness ws k));
            okk <- okk /\ y = nth witness cs k;
            Bd.b1 <- Bd.b1 \/ (!(nth 0 T k \in S.cs) /\ y = nth witness cs k
                               /\ incons S.toks (nth 0 T k) tok.`tk_msg (nth witness cs k)
                                         (nth witness ws k));
            k <- k + 1;
          }
          if (okk) {
            c <@ H.h((liftw (aggw ws), (S.t, tok.`tk_msg)));
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

module GameR (A : Adv) (H : HCO.QRO_i) (R : HCO.Repro_i) = {
  proc run() : bool = {
    var mu, sg, ok, sks, sds, cv;
    S.cs <@ A(CntH(HOR(H)), CntO(SOR(H, R))).corrupt();
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
    Ex.ix <- empty;
    Ex.n <- 0;
    Ex.dn <- [];
    Rx.nr <- 0;
    Rx.pts <- [];
    Rx.bP <- false;
    Rx.bC <- false;
    Rx.lop <- empty;
    Cnt.c0 <- 0;
    Cnt.c1 <- 0;
    Cnt.cc <- 0;
    Cnt.cs <- 0;
    sks <- fun j => if j \in S.cs then shr S.s S.p j else RqVec.Vector.zerov;
    sds <- fun (ab : pidx * pidx) =>
             if hpair S.cs (PIdx.val ab.`1) (PIdx.val ab.`2) then witness else S.sdc ab;
    (mu, sg) <@ A(CntH(HOR(H)), CntO(SOR(H, R))).forge(S.t, sks, sds);
    cv <@ H.h((liftw (rndw (mulA mA sg.`2 - rowZ sg.`1 (liftt S.t)) + sg.`3), (S.t, mu)));
    ok <- (cv = sg.`1 /\ inbnd sg.`2 sg.`3) /\ admc S.cs;
    return win4 S.cs S.lo mu ok /\ !Bd.b1 /\ !Bd.b2 /\ !Bd.b3
           /\ !H0C.extbad H0C.ER.ts H0C.ER.xs H0C.ER.cks;
  }
}.

module DR (A : Adv) (H : HCO.QRO_i) (R : HCO.Repro_i) = {
  proc main() : bool = {
    var b;
    H0H.QRO.init();
    H0H.LC.sv <- empty;
    H0H.LC.rv <- [];
    H0H.LC.fv <- empty;
    H0H.LC.lft <- true;
    H0H.CQ.n <- 0;
    H0C.QRO.init();
    H0C.Sim.init();
    H0C.ER.ts <- [];
    H0C.ER.xs <- [];
    H0C.ER.cks <- [];
    H0C.ER.simw <- true;
    H0C.CQ.n <- 0;
    H1O.QRO.init();
    b <@ GameR(A, H, R).run();
    return b;
  }
}.

op qc : int = qhc + qsig + 1.

(* Sums of a list with one entry replaced *)
lemma rowmap_put (f : row -> row) (l : row list) (p : int) (x : row) :
  0 <= p < size l =>
  rowmap f (put l p x) = f x + (rowmap f l - f (nth witness l p)).
proof.
elim: l p => [| a l ih] p /=; first by smt().
move=> [hp1 hp2].
case: (p = 0) => [-> | hne].
+ rewrite put_cons0 /= !rowmap_cons.
  have -> : f a + rowmap f l - f a = rowmap f l.
  - by rewrite RqRow.Vector.ZModule.addrAC RqRow.Vector.ZModule.subrr RqRow.Vector.ZModule.add0r.
  done.
rewrite put_consS // !rowmap_cons ih; first by smt().
rewrite RqRow.Vector.ZModule.addrCA; congr.
by rewrite RqRow.Vector.ZModule.addrA.
qed.

(* A fresh nonce determines its challenge point *)
lemma dpt1 (t : row) (m0 : msg) (ws : row list) (p : int) (s : vec * row) :
  mu1 (dpt t m0 ws p) (xpt t m0 (put ws p (popn s)), s) = mu1 dnp s.
proof.
by rewrite /dpt (in_dmap1E_can dnp _ (fun (a : hcin * (vec * row)) => a.`2)).
qed.

(* Sampled points are the points of their nonces *)
lemma dpt_supp (t : row) (m0 : msg) (ws : row list) (p : int) (a : hcin * (vec * row)) :
  a \in dpt t m0 ws p => a = (xpt t m0 (put ws p (popn a.`2)), a.`2).
proof. by rewrite /dpt supp_dmap => -[s] [_ ->]. qed.

(* Sampled points weigh as their nonces *)
lemma dpt_mu1 (t : row) (m0 : msg) (ws : row list) (p : int) (a : hcin * (vec * row)) :
  a \in dpt t m0 ws p => mu1 (dpt t m0 ws p) a = mu1 (dnonce `*` dnoiser) a.`2.
proof. by move=> /dpt_supp ->; rewrite dpt1. qed.

(* Every nonce gives a sampled point *)
lemma dpt_in (t : row) (m0 : msg) (ws : row list) (p : int) (s : vec * row) :
  s \in dnonce `*` dnoiser => (xpt t m0 (put ws p (popn s)), s) \in dpt t m0 ws p.
proof.
by move=> hs; rewrite /dpt; apply (dmap_supp dnp (fun s => (xpt t m0 (put ws p (popn s)), s)) s hs).
qed.

(* The fresh nonce distribution is lossless *)
lemma dpt_ll (t : row) (m0 : msg) (ws : row list) (p : int) : is_lossless (dpt t m0 ws p).
proof. by rewrite /dpt; apply dmap_ll; rewrite /dnp; exact dnp_ll. qed.

section RepHop.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -Fz, -Bd, -Ex, -Rx, -H0H.QRO, -H0C.QRO, -H1O.QRO,
                         -HCO.QRO, -H0H.LC, -H0H.CQ, -H0C.CQ, -H0C.Sim, -H0C.ER, -HCO.CQ,
                         -HCO.Rep}.

declare axiom A_bnd (H <: HOr {-A, -Cnt}) (O <: SOr {-A, -Cnt}) :
  hoare [A(CntH(H), CntO(O)).forge : Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 ==>
         Cnt.c0 <= qh0 /\ Cnt.c1 <= qh1 /\ Cnt.cc <= qhc /\ Cnt.cs <= qsig].

(* Regularity of an aggregate commitment in one fresh opening, the second part of the
   regularity lemma of the paper *)
declare axiom reg_agg (Y x : row) :
  mu dnp (fun (s : vec * row) => liftw (rndw (liftc (popn s) + Y)) = x) <= pw2.

(* The point fixed by a fresh nonce takes each value with small probability *)
lemma pmax_dpt (t : row) (m0 : msg) (ws : row list) (p : int) :
  0 <= p < size ws => HCO.pmaxok (dpt t m0 ws p) pw2.
proof.
move=> hp x; rewrite /dpt dmapE /(\o) /=.
apply (StdOrder.RealOrder.ler_trans
         (mu dnp (fun s => liftw (rndw (liftc (popn s)
                    + (rowmap liftc ws - liftc (nth witness ws p)))) = x.`1))).
+ by apply mu_sub => s /= <-; rewrite /xpt /aggw rowmap_put.
exact reg_agg.
qed.

(* The point fixed by a fresh nonce takes a given value with small probability *)
lemma pmax_dpt_x (t : row) (m0 : msg) (ws : row list) (p : int) (x : hcin) :
  0 <= p < size ws => mu (dpt t m0 ws p) (fun (a : hcin * (vec * row)) => a.`1 = x) <= pw2.
proof. by move=> hp; apply (pmax_dpt t m0 ws p hp). qed.

(* Second rounds agree when the reprogramming oracle only samples *)
equiv o2_r :
  SOE(H0C.ER).o2 ~ SOR(HCO.CQ, HCO.Rep).o2 :
  ={u, T, cs} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh}
  /\ !HCO.Rep.wld{2} /\ HCO.Rep.bnd{2} = qsig /\ HCO.Rep.pm{2} = pw2 /\ HCO.Rep.cnt{2} = Rx.nr{2} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh}
  /\ !HCO.Rep.wld{2} /\ HCO.Rep.bnd{2} = qsig /\ HCO.Rep.pm{2} = pw2 /\ HCO.Rep.cnt{2} = Rx.nr{2}.
proof.
proc.
seq 1 1 : (={u, T, cs, out} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh}
  /\ !HCO.Rep.wld{2} /\ HCO.Rep.bnd{2} = qsig /\ HCO.Rep.pm{2} = pw2 /\ HCO.Rep.cnt{2} = Rx.nr{2}); first by auto.
if => //.
seq 1 1 : (={u, T, cs, out, tok} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh}
  /\ !HCO.Rep.wld{2} /\ HCO.Rep.bnd{2} = qsig /\ HCO.Rep.pm{2} = pw2 /\ HCO.Rep.cnt{2} = Rx.nr{2}); first by auto.
if => //.
swap{1} [2..3] 3.
seq 3 4 : (={u, T, cs, out, tok, d} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh}
  /\ !HCO.Rep.wld{2} /\ HCO.Rep.bnd{2} = qsig /\ HCO.Rep.pm{2} = pw2 /\ HCO.Rep.cnt{2} = Rx.nr{2} /\ ok2 tok{2} T{2} cs{2}
           /\ vr{2} = (tok{2}.`tk_msg, T{2}, cs{2})); first by auto.
inline{1} SOE(H0C.ER).sub.
sp 1 0.
if; first by move=> /> /#.
+ inline{2} SOR(HCO.CQ, HCO.Rep).subm.
  seq 3 4 : (={u, T, cs, out, tok, d} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh}
  /\ !HCO.Rep.wld{2} /\ HCO.Rep.bnd{2} = qsig /\ HCO.Rep.pm{2} = pw2 /\ HCO.Rep.cnt{2} = Rx.nr{2} /\ ok2 tok{2} T{2} cs{2}
             /\ vr{2} = (tok{2}.`tk_msg, T{2}, cs{2})).
  + while (={k, u, T, cs, out, tok, d} /\ V{1} = V{2} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh}
  /\ !HCO.Rep.wld{2} /\ HCO.Rep.bnd{2} = qsig /\ HCO.Rep.pm{2} = pw2 /\ HCO.Rep.cnt{2} = Rx.nr{2} /\ ok2 tok{2} T{2} cs{2}
           /\ vr{2} = (tok{2}.`tk_msg, T{2}, cs{2})).
    + by wp; if => //; inline *; auto.
    auto => />.
  inline{1} H0H.LC.reveal H0H.LC.gsec.
  sp 2 0.
  case (u{1} \in H0H.LC.sv{1}).
  + rcondf{1} 1; first by auto.
    rcondf{2} 2.
    + by move=> &1; if; [inline *; sp; if; auto | auto].
    if{2}.
    + inline{2} HCO.Rep.reprog.
      rcondt{2} 3.
      + by move=> &1; auto => /> &hr *; apply pmax_dpt_x; rewrite size_map; smt(index_ge0 index_mem).
      rcondf{2} 5; first by auto.
      wp; rnd{2}; rnd{2}; auto => /> &1 &2 *.
      by rewrite dpt_ll HCO.dhash_ll /=; smt().
    by wp; rnd{2}; auto => /> &1 &2 *; rewrite /dnp dnp_ll /=.
  rcondt{1} 1; first by auto.
  rcondt{2} 2.
  + by move=> &1; if; [inline *; sp; if; auto | auto].
  if{2}.
  + inline{2} HCO.Rep.reprog.
    rcondt{2} 3.
    + by move=> &1; auto => /> &hr *; apply pmax_dpt_x; rewrite size_map; smt(index_ge0 index_mem).
    rcondf{2} 5; first by auto.
    wp; rnd{2}.
    rnd (fun (s : vec * row) =>
           (xpt S.t{2} vr{2}.`1 (put (wsV S.toks{2} S.req{2} S.cs{2} H0C.ER.xs{2} Ex.ix{2} vr{2})
                                     (index tok{2}.`tk_i T{2}) (popn s)), s))
        (fun (a : hcin * (vec * row)) => a.`2).
    auto => /> &1 &2 *.
    smt(dpt_supp dpt_mu1 dpt_in HCO.dhash_ll).
  by wp; rnd; auto => /> &1 &2 *; rewrite /dnp.
wp; call (_ : ={glob H0H.LC}); first by sim.
by auto.
qed.

(* Checks leave the reprogramming records alone *)
lemma chk_fr : hoare [SOE(H0C.ER).chk : !HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr ==> !HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr].
proof.
proc; if.
+ by if; inline *; auto.
by inline *; sp; if; [sp; if; auto | auto].
qed.

(* Adversary commitment queries leave the reprogramming records alone *)
lemma h0_fr : hoare [CntH(HOR(HCO.CQ)).h0 : !HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr ==> !HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr].
proof. by proc; inline *; sp; if; [auto | sp; if; [sp; if; auto | auto]]. qed.

(* First rounds leave the reprogramming records alone *)
lemma o1_fr : hoare [CntO(SOR(HCO.CQ, HCO.Rep)).o1 : !HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr ==> !HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr].
proof. by proc; inline *; sp; if; [sp; if; sp; if; auto | auto]. qed.

(* Third rounds leave the reprogramming records alone *)
lemma o3_fr : hoare [SOR(HCO.CQ, HCO.Rep).o3 : !HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr ==> !HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr].
proof.
proc; sp; if => //; sp; if => //; sp; if => //.
seq 4 : (!HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr); first by auto.
seq 1 : (!HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr).
+ while (!HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr); last by auto.
  by wp; call chk_fr; auto.
if => //.
seq 1 : (!HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr); first by inline *; auto.
seq 6 : (!HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr); first by wp; while (!HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr); auto.
by sp; if; [auto | if; auto].
qed.

(* Third rounds agree when the challenge is read through the counting oracle *)
equiv o3_eqr :
  SOE(H0C.ER).o3 ~ SOR(HCO.CQ, HCO.Rep).o3 :
  ={u, T, cs, ws} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh}.
proof.
proc.
seq 1 1 : (={u, T, cs, ws, out} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh}); first by auto.
if => //.
seq 1 1 : (={u, T, cs, ws, out, tok} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh}); first by auto.
if => //.
seq 1 1 : (={u, T, cs, ws, out, tok, d} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh}); first by auto.
if => //.
seq 5 5 : (={u, T, cs, ws, out, tok, d, okk, Ex.cur} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh}); first by sim.
if => //.
seq 1 1 : (={u, T, cs, ws, out, tok, d, okk, c, Ex.cur} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh}); first by inline *; auto.
by sim.
qed.

(* The extraction game is the reprogramming game when nothing is reprogrammed *)
lemma ge_gr &m :
  Pr[H0C.EG(DE(A)).main(true) @ &m : res /\ !H0C.extbad H0C.ER.ts H0C.ER.xs H0C.ER.cks]
  = Pr[HCO.RepG(DR(A)).main(false, qsig, pw2) @ &m : res].
proof.
byequiv => //; proc.
inline DE(A, H0C.ER).main DR(A, HCO.CQ, HCO.Rep).main GameE(A, H0C.ER).run
       GameR(A, HCO.CQ, HCO.Rep).run.
inline{2} HCO.CQ.h.
wp.
call (_ : ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh}
  /\ !HCO.Rep.wld{2} /\ HCO.Rep.bnd{2} = qsig /\ HCO.Rep.pm{2} = pw2 /\ HCO.Rep.cnt{2} = Rx.nr{2}).
+ conseq (_ : ={i, mu} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh}) _ o1_fr => //.
  by proc; inline *; sim.
+ by proc; wp; call o2_r; auto.
+ conseq (_ : ={u, T, cs, ws} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh}) _ (_ : !HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr ==> !HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr) => //.
  + by proc; sp; call o3_fr; auto.
  by proc; wp; call o3_eqr; auto.
+ conseq (_ : ={x} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh}) _ h0_fr => //.
  by proc; inline *; sim.
+ by proc; inline *; auto.
+ by proc; inline *; auto.
inline *.
swap{1} [8..13] -7.
swap{2} 1 19.
auto.
call (_ : true).
by auto => />; smt(H0C.sinit_ll).
qed.

(* Checks do not query the challenge oracle *)
lemma chk_cq (n : int) : hoare [SOE(H0C.ER).chk : HCO.CQ.n <= n ==> HCO.CQ.n <= n].
proof.
proc; if.
+ by if; inline *; auto.
by inline *; sp; if; [sp; if; auto | auto].
qed.

(* First rounds do not query the challenge oracle *)
lemma o1_cq (n : int) : hoare [SOR(HCO.CQ, HCO.Rep).o1 : HCO.CQ.n <= n ==> HCO.CQ.n <= n].
proof. by proc; inline *; sp; if; [sp; if; sp; if; auto | auto]. qed.

(* Second rounds do not query the challenge oracle *)
lemma o2_cq (n : int) : hoare [SOR(HCO.CQ, HCO.Rep).o2 : HCO.CQ.n <= n ==> HCO.CQ.n <= n].
proof.
proc; sp; if => //; sp; if => //; sp.
seq 1 : (HCO.CQ.n <= n).
+ if.
  + seq 1 : (HCO.CQ.n <= n).
    + by inline *; sp; while (HCO.CQ.n <= n); auto.
    by sp; if; [inline *; sp; if; auto | auto].
  by inline *; sp; if; auto.
by auto.
qed.

(* Third rounds query the challenge oracle at most once *)
lemma o3_cq (n : int) : hoare [SOR(HCO.CQ, HCO.Rep).o3 : HCO.CQ.n <= n ==> HCO.CQ.n <= n + 1].
proof.
proc; sp; if; last by auto => /#.
sp; if; last by auto => /#.
sp; if; last by auto => /#.
seq 4 : (HCO.CQ.n <= n); first by auto.
seq 1 : (HCO.CQ.n <= n).
+ while (HCO.CQ.n <= n); last by auto.
  by wp; call (chk_cq n); auto.
if; last by auto => /#.
seq 1 : (HCO.CQ.n <= n + 1); first by inline *; auto => /#.
seq 6 : (HCO.CQ.n <= n + 1); first by wp; while (HCO.CQ.n <= n + 1); auto.
by sp; if; [auto | if; auto].
qed.

(* The reprogramming game respects the challenge query budget *)
lemma dr_cnt : hoare [DR(A, HCO.CQ, HCO.Rep).main : HCO.CQ.n = 0 ==> HCO.CQ.n <= qc].
proof.
proc; inline GameR(A, HCO.CQ, HCO.Rep).run HCO.CQ.h; wp.
conseq (_ : _ ==> HCO.CQ.n <= Cnt.cc + Cnt.cs /\ Cnt.cc <= qhc /\ Cnt.cs <= qsig).
+ by move=> &hr _ /> *; rewrite /qc; smt().
call (_ : Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 /\ HCO.CQ.n = 0 ==>
          HCO.CQ.n <= Cnt.cc + Cnt.cs /\ Cnt.cc <= qhc /\ Cnt.cs <= qsig).
+ conseq (A_bnd (HOR(HCO.CQ)) (SOR(HCO.CQ, HCO.Rep)))
         (_ : HCO.CQ.n = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 ==> HCO.CQ.n <= Cnt.cc + Cnt.cs) => //.
  proc (HCO.CQ.n <= Cnt.cc + Cnt.cs) => //.
  + by proc; sp; ecall (o1_cq HCO.CQ.n); auto => /#.
  + by proc; sp; ecall (o2_cq HCO.CQ.n); auto => /#.
  + by proc; sp; ecall (o3_cq HCO.CQ.n); auto => /#.
  + by proc; inline *; sp; if; [auto | sp; if; [sp; if; auto | auto]] => /#.
  + by proc; inline *; auto.
  + by proc; inline *; auto => /#.
by auto; call (_ : true); inline *; auto.
qed.

(* The reprogramming bound is nonnegative *)
lemma ge0_pw2 : 0%r <= pw2.
proof. by have := reg_agg witness witness; smt(mu_bounded). qed.

(* Reprogramming the challenge of each complete request when it completes *)
lemma rep_hop &m :
  `|Pr[HCO.RepG(DR(A)).main(false, qsig, pw2) @ &m : res]
    - Pr[HCO.RepG(DR(A)).main(true, qsig, pw2) @ &m : res]|
  <= qsig%r * (sqrt (qc%r * pw2) + qc%r * pw2 / 2%r).
proof.
apply (HCO.ghhm (DR(A)) &m qc qsig pw2 _ ge0_qsig ge0_pw2 dr_cnt).
by rewrite /qc; smt(ge0_qhc ge0_qsig).
qed.

(* The extraction game is close to the reprogrammed game *)
lemma ge_rep &m :
  Pr[H0C.EG(DE(A)).main(true) @ &m : res /\ !H0C.extbad H0C.ER.ts H0C.ER.xs H0C.ER.cks]
  <= Pr[HCO.RepG(DR(A)).main(true, qsig, pw2) @ &m : res]
     + qsig%r * (sqrt (qc%r * pw2) + qc%r * pw2 / 2%r).
proof. by rewrite (ge_gr &m); have := rep_hop &m; smt(). qed.

end section RepHop.
