require import AllCore Int List Distr DList FMap FSet Real RealExp Finite StdOrder.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption.
require import Protocol Notions Privacy Extract FinEnum ChainBase ChainGame ChainCol ChainSim.
require import ChainDead ChainLazy ChainFlag ChainExt ChainRep.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

(* The programmed challenges: the challenge oracle after programming, the programmed values,
   the challenge and nonce of each complete
   request, the challenge used by each response, and the flag of a run where the responses
   cannot be simulated from hints *)
module Rp = {
  var fhp  : hcin -> rq
  var prog : (hcin, rq) fmap
  var cV   : (request, rq) fmap
  var sV   : (request, vec * row) fmap
  var cz   : (request * int, rq) fmap
  var bH   : bool
}.

(* The nonce part of each response that a hint replaces *)
module Rh = {
  var dz : (request * int, vec) fmap
}.

(* The conditions under which the last honest response of a request is computed from its hint:
   the request was completed by the token l of an honest member p with nonce part r, every
   other honest member responded with the challenge cv and with the nonce part of p only *)
op okclose (lop : (request, int) fmap) (sV : (request, vec * row) fmap) (cV : (request, rq) fmap)
           (toks : (int, token) fmap) (fz : (request * int, vec * vec) fmap)
           (cz : (request * int, rq) fmap) (dz : (request * int, vec) fmap)
           (C : corrset) (V : request) (T : committee) (i : int) (dzk : vec) : bool =
  let p = (oget toks.[oget lop.[V]]).`tk_i in
  let r = (oget sV.[V]).`1 in
  V \in lop /\ V \in sV /\ V \in cV /\ wf_nodes T /\ uniq (honest T C) /\ i \in honest T C
  /\ p \in honest T C
  /\ (forall a, a \in filter (fun a => a <> i) (honest T C) =>
        (V, a) \in fz /\ (V, a) \in cz /\ (V, a) \in dz /\ oget cz.[(V, a)] = oget cV.[V]
        /\ oget dz.[(V, a)] = (if a = p then r else RqVec.Vector.zerov))
  /\ dzk = (if i = p then r else RqVec.Vector.zerov).

(* The challenge oracle with its programmed points *)
op hcp (prog : (hcin, rq) fmap) (f : hcin -> rq) (x : hcin) : rq =
  if x \in prog then oget prog.[x] else f x.

module HOP : HOr = {
  proc h0 = HOE(H0C.ER).h0
  proc h1(x : h1in) : view = { return H1O.QRO.fh x; }
  proc hc(x : hcin) : rq = { return Rp.fhp x; }
}.

module SOP : SOr = {
  proc o1 = SOA(H0H.LC).o1

  proc o2(u : int, T : committee, cs : cmt list) : row option = {
    var out, tok, d, s, x, c, vr;
    out <- None;
    if (u \in S.toks) {
      tok <- oget S.toks.[u];
      if (ok2 tok T cs) {
        d <- H1O.QRO.fh (e1 S.t tok.`tk_msg T cs);
        vr <- (tok.`tk_msg, T, cs);
        S.req.[u] <- vr;
        S.lo <- (vr, tok.`tk_i) :: S.lo;
        if (complete vr S.cs S.lo /\ !(vr \in Ex.dn)) {
          SOR(HCO.CQ, HCO.Rep).subm(vr);
          Rp.bH <- Rp.bH \/ u \in H0H.LC.sv \/ (exists a, (vr, a) \in S.lr);
          if (Rx.nr < qsig) {
            s <$ dnp;
            x <- xpt S.t vr.`1 (put (wsV S.toks S.req S.cs H0C.ER.xs Ex.ix vr)
                                    (index tok.`tk_i T) (popn s));
            c <$ dchal;
            Rx.bP <- Rx.bP \/ x \in Rx.pts;
            Rx.pts <- x :: Rx.pts;
            Rx.nr <- Rx.nr + 1;
            Rp.fhp <- Rp.fhp.[x <- c];
            Rp.prog.[x] <- c;
            Rp.cV.[vr] <- c;
            Rp.sV.[vr] <- s;
          } else {
            Rx.bC <- true;
            s <$ dnp;
            Rp.sV.[vr] <- s;
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
    var out, tok, d, k, okk, y, c, z, mkh, mkc, j, v, ys, f, dzk;
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
            c <- Rp.fhp (liftw (aggw ws), (S.t, tok.`tk_msg));
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
            dzk <- if Rx.lop.[oget S.req.[u]] = Some u then tok.`tk_r else RqVec.Vector.zerov;
            Rp.bH <- Rp.bH \/ (oget S.req.[u], tok.`tk_i) \in S.lr
                   \/ (oget S.req.[u] \in Rp.cV /\ c <> oget Rp.cV.[oget S.req.[u]])
                   \/ (ys = [] /\ !(oget S.req.[u] \in Rp.cV))
                   \/ (oget S.req.[u] \in Rx.lop /\ oget Rx.lop.[oget S.req.[u]] <> u
                       /\ (oget S.toks.[oget Rx.lop.[oget S.req.[u]]]).`tk_i = tok.`tk_i)
                   \/ T <> (oget S.req.[u]).`2
                   \/ (ys = [] /\ !((oget S.req.[u], tok.`tk_i) \in S.lr)
                       /\ !okclose Rx.lop Rp.sV Rp.cV S.toks Fz.fz Rp.cz Rh.dz S.cs
                                    (oget S.req.[u]) T tok.`tk_i dzk);
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
              Rp.cz.[(oget S.req.[u], tok.`tk_i)] <- c;
              Rh.dz.[(oget S.req.[u], tok.`tk_i)] <- dzk;
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

module GP (A : Adv) = {
  proc main() : bool = {
    var mu, sg, ok, sks, sds, cv;
    HCO.QRO.init();
    Rp.fhp <- HCO.QRO.fh;
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
    S.cs <@ A(CntH(HOP), CntO(SOP)).corrupt();
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
    Rp.prog <- empty;
    Rp.cV <- empty;
    Rp.sV <- empty;
    Rp.cz <- empty;
    Rp.bH <- false;
    Rh.dz <- empty;
    Cnt.c0 <- 0;
    Cnt.c1 <- 0;
    Cnt.cc <- 0;
    Cnt.cs <- 0;
    sks <- fun j => if j \in S.cs then shr S.s S.p j else RqVec.Vector.zerov;
    sds <- fun (ab : pidx * pidx) =>
             if hpair S.cs (PIdx.val ab.`1) (PIdx.val ab.`2) then witness else S.sdc ab;
    (mu, sg) <@ A(CntH(HOP), CntO(SOP)).forge(S.t, sks, sds);
    cv <- Rp.fhp (liftw (rndw (mulA mA sg.`2 - rowZ sg.`1 (liftt S.t)) + sg.`3), (S.t, mu));
    ok <- (cv = sg.`1 /\ inbnd sg.`2 sg.`3) /\ admc S.cs;
    return win4 S.cs S.lo mu ok /\ !Bd.b1 /\ !Bd.b2 /\ !Bd.b3
           /\ !H0C.extbad H0C.ER.ts H0C.ER.xs H0C.ER.cks;
  }
}.

(* Sampled points carry nonces of the nonce distribution *)
lemma dpt_snd (t : row) (m0 : msg) (ws : row list) (p : int) (a : hcin * (vec * row)) :
  a \in dpt t m0 ws p => a.`2 \in dnp.
proof. by rewrite /dpt supp_dmap => -[s] [hs ->]. qed.

section ProgHop.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -Fz, -Bd, -Ex, -Rx, -Rp, -Rh, -H0H.QRO, -H0C.QRO,
                         -H1O.QRO, -HCO.QRO, -H0H.LC, -H0H.CQ, -H0C.CQ, -H0C.Sim, -H0C.ER,
                         -HCO.CQ, -HCO.Rep}.

declare axiom reg_agg (Y x : row) :
  mu dnp (fun (s : vec * row) => liftw (rndw (liftc (popn s) + Y)) = x) <= pw2.

(* The point fixed by a fresh nonce takes a given value with small probability *)
local lemma pmax_x (t : row) (m0 : msg) (ws : row list) (p : int) (x : hcin) :
  0 <= p < size ws => mu (dpt t m0 ws p) (fun (a : hcin * (vec * row)) => a.`1 = x) <= pw2.
proof.
move=> hp; rewrite /dpt dmapE /(\o) /=.
apply (StdOrder.RealOrder.ler_trans
         (mu dnp (fun s => liftw (rndw (liftc (popn s)
                    + (rowmap liftc ws - liftc (nth witness ws p)))) = x.`1))).
+ by apply mu_sub => s /= <-; rewrite /xpt /aggw rowmap_put.
exact reg_agg.
qed.

(* Second rounds agree when the reprogramming is replaced by programming *)
local equiv o2_p :
  SOR(HCO.CQ, HCO.Rep).o2 ~ SOP.o2 : ={u, T, cs} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop}
  /\ HCO.QRO.fh{1} = Rp.fhp{2} /\ HCO.Rep.wld{1} /\ HCO.Rep.bnd{1} = qsig /\ HCO.Rep.pm{1} = pw2 /\ HCO.Rep.cnt{1} = Rx.nr{1} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop}
  /\ HCO.QRO.fh{1} = Rp.fhp{2} /\ HCO.Rep.wld{1} /\ HCO.Rep.bnd{1} = qsig /\ HCO.Rep.pm{1} = pw2 /\ HCO.Rep.cnt{1} = Rx.nr{1}.
proof.
proc.
seq 1 1 : (={u, T, cs, out} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop}
  /\ HCO.QRO.fh{1} = Rp.fhp{2} /\ HCO.Rep.wld{1} /\ HCO.Rep.bnd{1} = qsig /\ HCO.Rep.pm{1} = pw2 /\ HCO.Rep.cnt{1} = Rx.nr{1}); first by auto.
if => //.
seq 1 1 : (={u, T, cs, out, tok} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop}
  /\ HCO.QRO.fh{1} = Rp.fhp{2} /\ HCO.Rep.wld{1} /\ HCO.Rep.bnd{1} = qsig /\ HCO.Rep.pm{1} = pw2 /\ HCO.Rep.cnt{1} = Rx.nr{1}); first by auto.
if => //.
seq 4 4 : (={u, T, cs, out, tok, d, vr} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop}
  /\ HCO.QRO.fh{1} = Rp.fhp{2} /\ HCO.Rep.wld{1} /\ HCO.Rep.bnd{1} = qsig /\ HCO.Rep.pm{1} = pw2 /\ HCO.Rep.cnt{1} = Rx.nr{1} /\ ok2 tok{2} T{2} cs{2}
           /\ vr{2} = (tok{2}.`tk_msg, T{2}, cs{2})); first by auto.
if => //.
+ seq 1 1 : (={u, T, cs, out, tok, d, vr} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop}
  /\ HCO.QRO.fh{1} = Rp.fhp{2} /\ HCO.Rep.wld{1} /\ HCO.Rep.bnd{1} = qsig /\ HCO.Rep.pm{1} = pw2 /\ HCO.Rep.cnt{1} = Rx.nr{1} /\ ok2 tok{2} T{2} cs{2}
             /\ vr{2} = (tok{2}.`tk_msg, T{2}, cs{2})).
  + call (_ : ={S.cs, Ex.ix, Ex.n, Ex.dn, glob H0C.ER, glob H0C.Sim}); first by sim.
    by auto.
  sp 0 1.
  if => //.
  + inline{1} HCO.Rep.reprog.
    rcondt{1} 3.
    + by move=> &2; auto => /> &hr *; apply pmax_x; rewrite size_map; smt(index_ge0 index_mem).
    rcondt{1} 5; first by auto.
    seq 3 1 : (={u, T, cs, out, tok, d, vr} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop}
  /\ HCO.QRO.fh{1} = Rp.fhp{2} /\ HCO.Rep.wld{1} /\ HCO.Rep.bnd{1} = qsig /\ HCO.Rep.pm{1} = pw2 /\ HCO.Rep.cnt{1} = Rx.nr{1} /\ ok2 tok{2} T{2} cs{2}
               /\ vr{2} = (tok{2}.`tk_msg, T{2}, cs{2}) /\ Rx.nr{2} < qsig
               /\ a0{1} = (xpt S.t{2} vr{2}.`1 (put (wsV S.toks{2} S.req{2} S.cs{2} H0C.ER.xs{2}
                                                    Ex.ix{2} vr{2}) (index tok{2}.`tk_i T{2})
                                               (popn s{2})), s{2})).
    + rnd (fun (a : hcin * (vec * row)) => a.`2)
          (fun (s : vec * row) =>
             (xpt S.t{2} vr{2}.`1 (put (wsV S.toks{2} S.req{2} S.cs{2} H0C.ER.xs{2} Ex.ix{2} vr{2})
                                       (index tok{2}.`tk_i T{2}) (popn s)), s)).
      auto => /> &1 &2 *.
      split; first by move=> sR _; rewrite dpt1.
      move=> _ a0L ha; split; first exact (dpt_snd _ _ _ _ _ ha).
      by move=> _; exact (dpt_supp _ _ _ _ _ ha).
    seq 1 2 : (={u, T, cs, out, tok, d, vr} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop}
  /\ HCO.QRO.fh{1} = Rp.fhp{2} /\ HCO.Rep.wld{1} /\ HCO.Rep.bnd{1} = qsig /\ HCO.Rep.pm{1} = pw2 /\ HCO.Rep.cnt{1} = Rx.nr{1} /\ ok2 tok{2} T{2} cs{2}
               /\ vr{2} = (tok{2}.`tk_msg, T{2}, cs{2}) /\ Rx.nr{2} < qsig
               /\ a0{1} = (x{2}, s{2}) /\ y{1} = c{2}).
    + by rnd; auto.
    by auto => /> /#.
  by auto.
by wp; call (_ : ={glob H0H.LC}); [sim | auto].
qed.

(* Checks leave the reprogramming state alone *)
local lemma chk_rl : hoare [SOE(H0C.ER).chk : HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr ==> HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr].
proof.
proc; if.
+ by if; inline *; auto.
by inline *; sp; if; [sp; if; auto | auto].
qed.

(* Third rounds agree when the challenge is read from the programmed oracle *)
local equiv o3_p :
  SOR(HCO.CQ, HCO.Rep).o3 ~ SOP.o3 : ={u, T, cs, ws} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop}
  /\ HCO.QRO.fh{1} = Rp.fhp{2} /\ HCO.Rep.wld{1} /\ HCO.Rep.bnd{1} = qsig /\ HCO.Rep.pm{1} = pw2 /\ HCO.Rep.cnt{1} = Rx.nr{1} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop}
  /\ HCO.QRO.fh{1} = Rp.fhp{2} /\ HCO.Rep.wld{1} /\ HCO.Rep.bnd{1} = qsig /\ HCO.Rep.pm{1} = pw2 /\ HCO.Rep.cnt{1} = Rx.nr{1}.
proof.
proc.
seq 1 1 : (={u, T, cs, ws, out} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop}
  /\ HCO.QRO.fh{1} = Rp.fhp{2} /\ HCO.Rep.wld{1} /\ HCO.Rep.bnd{1} = qsig /\ HCO.Rep.pm{1} = pw2 /\ HCO.Rep.cnt{1} = Rx.nr{1}); first by auto.
if => //.
seq 1 1 : (={u, T, cs, ws, out, tok} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop}
  /\ HCO.QRO.fh{1} = Rp.fhp{2} /\ HCO.Rep.wld{1} /\ HCO.Rep.bnd{1} = qsig /\ HCO.Rep.pm{1} = pw2 /\ HCO.Rep.cnt{1} = Rx.nr{1}); first by auto.
if => //.
seq 1 1 : (={u, T, cs, ws, out, tok, d} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop}
  /\ HCO.QRO.fh{1} = Rp.fhp{2} /\ HCO.Rep.wld{1} /\ HCO.Rep.bnd{1} = qsig /\ HCO.Rep.pm{1} = pw2 /\ HCO.Rep.cnt{1} = Rx.nr{1}); first by auto.
if => //.
seq 5 5 : (={u, T, cs, ws, out, tok, d, okk, Ex.cur} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop}
  /\ HCO.QRO.fh{1} = Rp.fhp{2} /\ HCO.Rep.wld{1} /\ HCO.Rep.bnd{1} = qsig /\ HCO.Rep.pm{1} = pw2 /\ HCO.Rep.cnt{1} = Rx.nr{1}).
+ conseq (_ : ={u, T, cs, ws, out, tok, d} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop} /\ HCO.QRO.fh{1} = Rp.fhp{2}
             ==> ={u, T, cs, ws, out, tok, d, okk, Ex.cur} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop}
                 /\ HCO.QRO.fh{1} = Rp.fhp{2})
         (_ : HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr ==> HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr) _ => //.
  + by wp; while (HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr); [wp; call chk_rl; auto | auto].
  by sim.
if => //.
seq 1 1 : (={u, T, cs, ws, out, tok, d, okk, c, Ex.cur} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop}
  /\ HCO.QRO.fh{1} = Rp.fhp{2} /\ HCO.Rep.wld{1} /\ HCO.Rep.bnd{1} = qsig /\ HCO.Rep.pm{1} = pw2 /\ HCO.Rep.cnt{1} = Rx.nr{1}); first by inline *; auto.
conseq (_ : ={u, T, cs, ws, out, tok, d, okk, c, Ex.cur} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop} /\ HCO.QRO.fh{1} = Rp.fhp{2}
             ==> ={out} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop} /\ HCO.QRO.fh{1} = Rp.fhp{2})
       (_ : HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr ==> HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr) _ => //.
+ seq 6 : (HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr); first by wp; while (HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr); auto.
  by sp; if; [auto | if; auto].
by sim.
qed.

(* First rounds leave the reprogramming state alone *)
local lemma o1_rl : hoare [CntO(SOR(HCO.CQ, HCO.Rep)).o1 : HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr ==> HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr].
proof. by proc; inline *; sp; if; [sp; if; sp; if; auto | auto]. qed.

(* Adversary commitment queries leave the reprogramming state alone *)
local lemma h0_rl : hoare [CntH(HOR(HCO.CQ)).h0 : HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr ==> HCO.Rep.wld /\ HCO.Rep.bnd = qsig /\ HCO.Rep.pm = pw2 /\ HCO.Rep.cnt = Rx.nr].
proof. by proc; inline *; sp; if; [auto | sp; if; [sp; if; auto | auto]]. qed.

(* The reprogrammed game is the game with explicit programming *)
lemma rep_gp &m :
  Pr[HCO.RepG(DR(A)).main(true, qsig, pw2) @ &m : res] = Pr[GP(A).main() @ &m : res].
proof.
byequiv => //; proc.
inline DR(A, HCO.CQ, HCO.Rep).main GameR(A, HCO.CQ, HCO.Rep).run.
inline{1} HCO.CQ.h.
wp.
call (_ : ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop}
  /\ HCO.QRO.fh{1} = Rp.fhp{2} /\ HCO.Rep.wld{1} /\ HCO.Rep.bnd{1} = qsig /\ HCO.Rep.pm{1} = pw2 /\ HCO.Rep.cnt{1} = Rx.nr{1}).
+ conseq (_ : ={i, mu} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop} /\ HCO.QRO.fh{1} = Rp.fhp{2}
             ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop} /\ HCO.QRO.fh{1} = Rp.fhp{2}) o1_rl _ => //.
  by proc; inline *; sim (: HCO.QRO.fh{1} = Rp.fhp{2}).
+ by proc; wp; call o2_p; auto.
+ by proc; wp; call o3_p; auto.
+ conseq (_ : ={x} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop} /\ HCO.QRO.fh{1} = Rp.fhp{2}
             ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO,
      glob H0C.CQ, glob H0C.Sim, glob H0C.ER, glob H1O.QRO, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop} /\ HCO.QRO.fh{1} = Rp.fhp{2}) h0_rl _ => //.
  by proc; inline *; sim (: HCO.QRO.fh{1} = Rp.fhp{2}).
+ by proc; inline *; auto.
+ by proc; inline *; auto.
inline *; auto.
call (_ : true).
by auto => />.
qed.

end section ProgHop.
