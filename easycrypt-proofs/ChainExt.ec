require import AllCore Int List Distr DList FMap FSet Real RealExp Finite StdOrder.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption.
require import Protocol Notions Privacy Extract FinEnum ChainBase ChainGame ChainCol ChainSim.
require import ChainDead ChainLazy ChainFlag.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

(* The extraction records: the submission index of each corrupt entry of a complete request,
   the number of submissions, the complete requests, and the request of the current check *)
module Ex = {
  var ix   : (request * int, int) fmap
  var n    : int
  var dn   : request list
  var cur  : request
}.

(* A request is complete once every honest member of its committee has opened it *)
op complete (V : request) (C : corrset) (L : alog) : bool =
  all (fun j => (V, j) \in L) (honest V.`2 C).

module HOE (O : H0C.ExtO) : HOr = {
  proc h0(x : h0in) : cmt = {
    var y;
    if (PIdx.val x.`1.`2 \in S.cs) { y <@ O.h(x); } else { y <@ H0H.LC.h(x); }
    return y;
  }
  proc h1(x : h1in) : view = { return H1O.QRO.fh x; }
  proc hc(x : hcin) : rq = { return HCO.QRO.fh x; }
}.

module SOE (O : H0C.ExtO) : SOr = {
  proc chk(x : h0in) : cmt = {
    var y;
    if (PIdx.val x.`1.`2 \in S.cs) {
      if ((Ex.cur, PIdx.val x.`1.`2) \in Ex.ix) {
        y <@ O.check(oget Ex.ix.[(Ex.cur, PIdx.val x.`1.`2)], x);
      } else {
        y <@ O.h(x);
      }
    } else {
      y <@ H0H.LC.h(x);
    }
    return y;
  }

  proc sub(V : request) : unit = {
    var k;
    if (complete V S.cs S.lo /\ !(V \in Ex.dn)) {
      Ex.dn <- V :: Ex.dn;
      k <- 0;
      while (k < size V.`2) {
        if (nth 0 V.`2 k \in S.cs) {
          Ex.ix.[(V, nth 0 V.`2 k)] <- Ex.n;
          O.submit(nth witness V.`3 k);
          Ex.n <- Ex.n + 1;
        }
        k <- k + 1;
      }
    }
  }

  proc o1 = SOA(H0H.LC).o1

  proc o2(u : int, T : committee, cs : cmt list) : row option = {
    var out, tok, d, s;
    out <- None;
    if (u \in S.toks) {
      tok <- oget S.toks.[u];
      if (ok2 tok T cs) {
        d <- H1O.QRO.fh (e1 S.t tok.`tk_msg T cs);
        s <@ H0H.LC.reveal(u);
        S.toks.[u] <- {| tok with tk_r = s.`1; tk_e = s.`2; tk_wbar = popn s; tk_phase = 2;
                                  tk_T = T; tk_dig = d |};
        S.req.[u] <- (tok.`tk_msg, T, cs);
        S.lo <- ((tok.`tk_msg, T, cs), tok.`tk_i) :: S.lo;
        sub((tok.`tk_msg, T, cs));
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
            y <@ chk((((S.t, tok.`tk_msg), toidx (nth 0 T k)), nth witness ws k));
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

module GameE (A : Adv) (O : H0C.ExtO) = {
  proc run() : bool = {
    var mu, sg, ok, sks, sds;
    S.cs <@ A(CntH(HOE(O)), CntO(SOE(O))).corrupt();
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
    Cnt.c0 <- 0;
    Cnt.c1 <- 0;
    Cnt.cc <- 0;
    Cnt.cs <- 0;
    sks <- fun j => if j \in S.cs then shr S.s S.p j else RqVec.Vector.zerov;
    sds <- fun (ab : pidx * pidx) =>
             if hpair S.cs (PIdx.val ab.`1) (PIdx.val ab.`2) then witness else S.sdc ab;
    (mu, sg) <@ A(CntH(HOE(O)), CntO(SOE(O))).forge(S.t, sks, sds);
    ok <- verify (hcof HCO.QRO.fh) S.t mu sg /\ admc S.cs;
    return win4 S.cs S.lo mu ok /\ !Bd.b1 /\ !Bd.b2 /\ !Bd.b3;
  }
}.

module DE (A : Adv) (O : H0C.ExtO) = {
  proc main() : bool = {
    var b;
    H0H.QRO.init();
    H0H.LC.sv <- empty;
    H0H.LC.rv <- [];
    H0H.LC.fv <- empty;
    H0H.LC.lft <- true;
    H0H.CQ.n <- 0;
    H1O.QRO.init();
    HCO.QRO.init();
    b <@ GameE(A, O).run();
    return b;
  }
}.

(* Updates within the size bound keep committee sizes bounded *)
lemma tokinv_upd (m : (int, token) fmap) (k : int) (tok : token) :
  tokinv m => size tok.`tk_T <= tthr => tokinv m.[k <- tok].
proof.
move=> hm ht u; rewrite mem_set get_setE.
by case: (u = k) => /= [_ | hne hu]; [exact ht | exact (hm u hu)].
qed.

(* Answered second rounds carry full committees *)
lemma ok2_size (tok : token) (T : committee) (cs : cmt list) : ok2 tok T cs => size T = tthr.
proof. by rewrite /ok2 /wf_committee. qed.

(* Multiplying by the threshold is monotone *)
lemma tmul_mono (a b : int) : a <= b => tthr * a <= tthr * b.
proof. by move=> h; apply StdOrder.IntOrder.ler_wpmul2l; smt(thr_range). qed.

op qx : int = qh0 + tthr * qsig.

op lx : int = tthr * qsig.

section ExtHop.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -Fz, -Bd, -Ex, -H0H.QRO, -H0C.QRO, -H1O.QRO,
                         -HCO.QRO, -H0H.LC, -H0H.CQ, -H0C.CQ, -H0C.Sim, -H0C.ER}.

declare axiom A_bnd (H <: HOr {-A, -Cnt}) (O <: SOr {-A, -Cnt}) :
  hoare [A(CntH(H), CntO(O)).forge : Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 ==>
         Cnt.c0 <= qh0 /\ Cnt.c1 <= qh1 /\ Cnt.cc <= qhc /\ Cnt.cs <= qsig].

(* Checks through the extraction interface agree with the oracle when nothing is simulated *)
equiv chk_e :
  SOA(H0H.LC).h0any ~ SOE(H0C.ER).chk :
  ={x, S.cs, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, H0C.QRO.fh} /\ !H0C.ER.simw{2}
  ==> ={res, S.cs, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, H0C.QRO.fh} /\ !H0C.ER.simw{2}.
proof.
proc; inline SOL(H0H.LC).h0any; sp.
if => //.
+ by if{2}; inline *; auto; smt().
call (_ : ={x, glob H0H.LC, glob H0H.QRO, glob H0H.CQ}
          ==> ={res, glob H0H.LC, glob H0H.QRO, glob H0H.CQ}); first by sim.
by auto.
qed.

(* Submissions leave the game state unchanged *)
lemma sub_ll : islossless SOE(H0C.ER).sub.
proof.
proc; sp; if => //.
while (true) (size V.`2 - k).
+ move=> z; wp; if; last by auto => /#.
  by inline *; auto => /#.
by auto => /#.
qed.

(* The game state outside the extraction records survives submissions *)
lemma sub_frame (st : (int, token) fmap) (rq : (int, request) fmap) (lo lr : alog) (ct : int) :
  hoare [SOE(H0C.ER).sub : S.toks = st /\ S.req = rq /\ S.lo = lo /\ S.lr = lr /\ S.ctr = ct
         ==> S.toks = st /\ S.req = rq /\ S.lo = lo /\ S.lr = lr /\ S.ctr = ct].
proof.
proc; sp; if => //.
while (S.toks = st /\ S.req = rq /\ S.lo = lo /\ S.lr = lr /\ S.ctr = ct).
+ by wp; if; [inline *; auto | auto].
by auto.
qed.


(* Submissions keep everything outside the extraction records *)
lemma sub_eq (gs : glob S) (gc : glob Cnt) (gf : glob Fz) (gb : glob Bd) (gl : glob H0H.LC)
             (gq : glob H0H.QRO) (gn : glob H0H.CQ) (g1 : glob H1O.QRO) (gh : glob HCO.QRO)
             (fc : h0in -> cmt) (w : bool) :
  phoare [SOE(H0C.ER).sub :
          (glob S) = gs /\ (glob Cnt) = gc /\ (glob Fz) = gf /\ (glob Bd) = gb
          /\ (glob H0H.LC) = gl /\ (glob H0H.QRO) = gq /\ (glob H0H.CQ) = gn
          /\ (glob H1O.QRO) = g1 /\ (glob HCO.QRO) = gh /\ H0C.QRO.fh = fc /\ H0C.ER.simw = w
          ==> (glob S) = gs /\ (glob Cnt) = gc /\ (glob Fz) = gf /\ (glob Bd) = gb
          /\ (glob H0H.LC) = gl /\ (glob H0H.QRO) = gq /\ (glob H0H.CQ) = gn
          /\ (glob H1O.QRO) = g1 /\ (glob HCO.QRO) = gh /\ H0C.QRO.fh = fc /\ H0C.ER.simw = w]
  = 1%r.
proof.
conseq sub_ll (_ : (glob S) = gs /\ (glob Cnt) = gc /\ (glob Fz) = gf /\ (glob Bd) = gb
          /\ (glob H0H.LC) = gl /\ (glob H0H.QRO) = gq /\ (glob H0H.CQ) = gn
          /\ (glob H1O.QRO) = g1 /\ (glob HCO.QRO) = gh /\ H0C.QRO.fh = fc /\ H0C.ER.simw = w
          ==> (glob S) = gs /\ (glob Cnt) = gc /\ (glob Fz) = gf /\ (glob Bd) = gb
          /\ (glob H0H.LC) = gl /\ (glob H0H.QRO) = gq /\ (glob H0H.CQ) = gn
          /\ (glob H1O.QRO) = g1 /\ (glob HCO.QRO) = gh /\ H0C.QRO.fh = fc /\ H0C.ER.simw = w) => //.
proc; sp; if => //.
while ((glob S) = gs /\ (glob Cnt) = gc /\ (glob Fz) = gf /\ (glob Bd) = gb
       /\ (glob H0H.LC) = gl /\ (glob H0H.QRO) = gq /\ (glob H0H.CQ) = gn
       /\ (glob H1O.QRO) = g1 /\ (glob HCO.QRO) = gh /\ H0C.QRO.fh = fc /\ H0C.ER.simw = w).
+ by wp; if; [inline *; auto | auto].
by auto.
qed.

(* Second rounds agree when nothing is simulated *)
equiv o2_e :
  SOL(H0H.LC).o2 ~ SOE(H0C.ER).o2 :
  ={u, T, cs} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H1O.QRO, glob HCO.QRO, H0C.QRO.fh}
  /\ !H0C.ER.simw{2} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H1O.QRO, glob HCO.QRO, H0C.QRO.fh}
  /\ !H0C.ER.simw{2}.
proof.
proc.
seq 1 1 : (={u, T, cs, out} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H1O.QRO, glob HCO.QRO, H0C.QRO.fh}
  /\ !H0C.ER.simw{2}); first by auto.
if => //.
seq 1 1 : (={u, T, cs, out, tok} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H1O.QRO, glob HCO.QRO, H0C.QRO.fh}
  /\ !H0C.ER.simw{2}); first by auto.
if => //.
seq 5 5 : (={u, T, cs, out, tok, d, s} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H1O.QRO, glob HCO.QRO, H0C.QRO.fh}
  /\ !H0C.ER.simw{2}).
+ wp; call (_ : ={glob H0H.LC}); first by sim.
  by auto.
wp.
exlim (glob S){2}, (glob Cnt){2}, (glob Fz){2}, (glob Bd){2}, (glob H0H.LC){2},
      (glob H0H.QRO){2}, (glob H0H.CQ){2}, (glob H1O.QRO){2}, (glob HCO.QRO){2},
      H0C.QRO.fh{2}, H0C.ER.simw{2} => gs gc gf gb gl gq gn g1 gh fc w.
call{2} (sub_eq gs gc gf gb gl gq gn g1 gh fc w).
by auto => /> /#.
qed.

(* Third rounds agree when nothing is simulated *)
equiv o3_e :
  SOA(H0H.LC).o3 ~ SOE(H0C.ER).o3 :
  ={u, T, cs, ws} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H1O.QRO, glob HCO.QRO, H0C.QRO.fh}
  /\ !H0C.ER.simw{2} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H1O.QRO, glob HCO.QRO, H0C.QRO.fh}
  /\ !H0C.ER.simw{2}.
proof.
proc.
seq 1 1 : (={u, T, cs, ws, out} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H1O.QRO, glob HCO.QRO, H0C.QRO.fh}
  /\ !H0C.ER.simw{2}); first by auto.
if => //.
seq 1 1 : (={u, T, cs, ws, out, tok} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H1O.QRO, glob HCO.QRO, H0C.QRO.fh}
  /\ !H0C.ER.simw{2}); first by auto.
if => //.
seq 1 1 : (={u, T, cs, ws, out, tok, d} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H1O.QRO, glob HCO.QRO, H0C.QRO.fh}
  /\ !H0C.ER.simw{2}); first by auto.
if => //.
seq 3 4 : (={u, T, cs, ws, out, tok, d, okk, k} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H1O.QRO, glob HCO.QRO, H0C.QRO.fh}
  /\ !H0C.ER.simw{2}); first by auto.
seq 1 1 : (={u, T, cs, ws, out, tok, d, okk} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H1O.QRO, glob HCO.QRO, H0C.QRO.fh}
  /\ !H0C.ER.simw{2}).
+ while (={u, T, cs, ws, out, tok, d, okk, k} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H1O.QRO, glob HCO.QRO, H0C.QRO.fh}
  /\ !H0C.ER.simw{2}); last by auto.
  by wp; call chk_e; auto.
conseq (_ : ={u, T, cs, ws, out, tok, d, okk} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H1O.QRO, glob HCO.QRO, H0C.QRO.fh}
             ==> ={out, S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H1O.QRO, glob HCO.QRO, H0C.QRO.fh})
       _ (_ : !H0C.ER.simw ==> !H0C.ER.simw) => //.
+ if => //.
  seq 7 : (!H0C.ER.simw); first by wp; while (!H0C.ER.simw); auto.
  by if; [auto | if; auto].
by sim.
qed.

(* The flagged lazy game is the extraction game without simulation *)
lemma ga_ge &m :
  Pr[H0H.LCG(BA(A)).main(true) @ &m : res /\ !Bd.b1 /\ !Bd.b2 /\ !Bd.b3]
  = Pr[H0C.EG(DE(A)).main(false) @ &m : res].
proof.
byequiv => //; proc.
inline BA(A, H0H.LC).main DE(A, H0C.ER).main GameA(A, H0H.LC).run GameE(A, H0C.ER).run.
wp.
call (_ : ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H1O.QRO, glob HCO.QRO, H0C.QRO.fh}
  /\ !H0C.ER.simw{2}).
+ conseq (_ : ={i, mu} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H1O.QRO, glob HCO.QRO, H0C.QRO.fh}
                ==> ={res, S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz,
      glob Bd, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H1O.QRO, glob HCO.QRO, H0C.QRO.fh})
         _ (_ : !H0C.ER.simw ==> !H0C.ER.simw) => //.
  + by proc; inline *; sp; if; [sp; if; sp; if; auto | auto].
  by proc; inline *; sim.
+ by proc; wp; call o2_e; auto.
+ by proc; wp; call o3_e; auto.
+ proc; inline HOL(H0H.LC).h0 HOE(H0C.ER).h0; sp; if => //.
  + by inline *; auto; smt().
  wp; call (_ : ={x, glob H0H.LC, glob H0H.QRO, glob H0H.CQ}
            ==> ={res, glob H0H.LC, glob H0H.QRO, glob H0H.CQ}); first by sim.
  by auto.
+ by proc; inline *; auto.
+ by proc; inline *; auto.
inline *.
swap{2} 1 12.
auto.
call (_ : true).
auto => />; smt(H0C.sinit_ll).
qed.

(* Submissions add at most one extraction per committee member *)
lemma sub_cnt (n m : int) :
  hoare [SOE(H0C.ER).sub : H0C.CQ.n <= n /\ size H0C.ER.ts <= m /\ size V.`2 <= tthr
         ==> H0C.CQ.n <= n /\ size H0C.ER.ts <= m + tthr].
proof.
proc; sp; if; last by auto; smt(thr_range).
while (H0C.CQ.n <= n /\ size H0C.ER.ts <= m + k /\ 0 <= k <= size V.`2 /\ size V.`2 <= tthr).
+ wp; if; last by auto; smt(thr_range).
  by inline *; auto => />; smt(size_rcons).
by auto; smt(thr_range size_ge0).
qed.

(* Honest commitment queries leave the simulated oracle alone *)
lemma lch_frame (n m : int) :
  hoare [H0H.LC.h : H0C.CQ.n <= n /\ size H0C.ER.ts <= m
         ==> H0C.CQ.n <= n /\ size H0C.ER.ts <= m].
proof. by proc; sp; if; [inline *; sp; if; auto | auto]. qed.

(* Checks query the simulated oracle at most once *)
lemma chk_cnt (n m : int) :
  hoare [SOE(H0C.ER).chk : H0C.CQ.n <= n /\ size H0C.ER.ts <= m
         ==> H0C.CQ.n <= n + 1 /\ size H0C.ER.ts <= m].
proof.
proc; if.
+ if; inline *; auto => /#.
by call (lch_frame n m); auto => /#.
qed.

(* First rounds do not query the simulated oracle *)
lemma o1_ec (n m : int) :
  hoare [SOE(H0C.ER).o1 : H0C.CQ.n <= n /\ size H0C.ER.ts <= m /\ tokinv S.toks
         ==> H0C.CQ.n <= n /\ size H0C.ER.ts <= m /\ tokinv S.toks].
proof.
proc; inline *; sp; if; last by auto.
sp; if.
+ by sp; if; auto => /> &hr *; apply tokinv_upd => //=; smt(thr_range).
by sp; if; auto => /> &hr *; apply tokinv_upd => //=; smt(thr_range).
qed.

(* Second rounds submit at most one extraction per member *)
lemma o2_ec (n m : int) :
  hoare [SOE(H0C.ER).o2 : H0C.CQ.n <= n /\ size H0C.ER.ts <= m /\ tokinv S.toks
         ==> H0C.CQ.n <= n /\ size H0C.ER.ts <= m + tthr /\ tokinv S.toks].
proof.
proc; sp; if; last by auto; smt(thr_range).
sp; if; last by auto; smt(thr_range).
wp; ecall (sub_cnt H0C.CQ.n (size H0C.ER.ts)).
inline *; sp; if; auto => /> &hr *; smt(tokinv_upd ok2_size).
qed.

(* Third rounds query the simulated oracle once per member *)
lemma o3_ec (n m : int) :
  hoare [SOE(H0C.ER).o3 : H0C.CQ.n <= n /\ size H0C.ER.ts <= m /\ tokinv S.toks
         ==> H0C.CQ.n <= n + tthr /\ size H0C.ER.ts <= m /\ tokinv S.toks].
proof.
proc; seq 1 : (H0C.CQ.n <= n /\ size H0C.ER.ts <= m /\ tokinv S.toks); first by auto.
if; last by auto; smt(thr_range).
seq 1 : (H0C.CQ.n <= n /\ size H0C.ER.ts <= m /\ tokinv S.toks /\ tok = oget S.toks.[u]
         /\ u \in S.toks); first by auto.
if; last by auto; smt(thr_range).
seq 1 : (H0C.CQ.n <= n /\ size H0C.ER.ts <= m /\ tokinv S.toks /\ tok = oget S.toks.[u]
         /\ u \in S.toks /\ T = tok.`tk_T); first by auto => /> /#.
if; last by auto; smt(thr_range).
seq 4 : (H0C.CQ.n <= n /\ size H0C.ER.ts <= m /\ tokinv S.toks /\ tok = oget S.toks.[u]
         /\ u \in S.toks /\ T = tok.`tk_T /\ k = 0); first by auto.
seq 1 : (H0C.CQ.n <= n + tthr /\ size H0C.ER.ts <= m /\ tokinv S.toks /\ tok = oget S.toks.[u]
         /\ u \in S.toks /\ T = tok.`tk_T).
+ while (H0C.CQ.n <= n + k /\ 0 <= k <= size T /\ size T <= tthr /\ size H0C.ER.ts <= m
         /\ tokinv S.toks /\ tok = oget S.toks.[u] /\ u \in S.toks /\ T = tok.`tk_T).
  + by wp; ecall (chk_cnt H0C.CQ.n (size H0C.ER.ts)); auto => /#.
  auto => /> &hr hn hm ht hu; split; first by rewrite size_ge0 /=; exact (ht u{hr} hu).
  smt().
if; last by auto.
seq 6 : (H0C.CQ.n <= n + tthr /\ size H0C.ER.ts <= m /\ tokinv S.toks /\ tok = oget S.toks.[u]
         /\ u \in S.toks /\ T = tok.`tk_T).
+ by while (H0C.CQ.n <= n + tthr /\ size H0C.ER.ts <= m /\ tokinv S.toks
            /\ tok = oget S.toks.[u] /\ u \in S.toks /\ T = tok.`tk_T); auto.
sp; if.
+ by auto => /> &hr hn hm ht hu *; apply tokinv_upd => //; rewrite /erase /=; exact (ht u{hr} hu).
if.
+ by auto => /> &hr hn hm ht hu *; apply tokinv_upd => //; rewrite /erase /=; exact (ht u{hr} hu).
by auto => /> &hr hn hm ht hu *; apply tokinv_upd => //; rewrite /erase /=; exact (ht u{hr} hu).
qed.

(* Adversary queries reach the simulated oracle at most once *)
lemma h0_ec (n m : int) :
  hoare [HOE(H0C.ER).h0 : H0C.CQ.n <= n /\ size H0C.ER.ts <= m
         ==> H0C.CQ.n <= n + 1 /\ size H0C.ER.ts <= m].
proof. by proc; if; [inline *; auto => /# | call (lch_frame n m); auto => /#]. qed.

(* The extraction game respects the query and extraction budgets *)
lemma de_cnt :
  hoare [DE(A, H0C.ER).main : H0C.CQ.n = 0 /\ H0C.ER.ts = [] ==>
         H0C.CQ.n <= qx /\ size H0C.ER.ts <= lx].
proof.
proc; inline GameE(A, H0C.ER).run; wp.
conseq (_ : _ ==> H0C.CQ.n <= Cnt.c0 + tthr * Cnt.cs /\ size H0C.ER.ts <= tthr * Cnt.cs
                  /\ Cnt.c0 <= qh0 /\ Cnt.cs <= qsig).
+ move=> &hr _ /=; rewrite /qx /lx => *.
  smt(tmul_mono).
call (_ : Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 /\ H0C.CQ.n = 0
          /\ size H0C.ER.ts = 0 /\ tokinv S.toks ==>
          H0C.CQ.n <= Cnt.c0 + tthr * Cnt.cs /\ size H0C.ER.ts <= tthr * Cnt.cs
          /\ tokinv S.toks /\ Cnt.c0 <= qh0 /\ Cnt.cs <= qsig).
+ conseq (A_bnd (HOE(H0C.ER)) (SOE(H0C.ER)))
         (_ : H0C.CQ.n = 0 /\ Cnt.c0 = 0 /\ Cnt.cs = 0 /\ size H0C.ER.ts = 0 /\ tokinv S.toks ==>
              H0C.CQ.n <= Cnt.c0 + tthr * Cnt.cs /\ size H0C.ER.ts <= tthr * Cnt.cs
              /\ tokinv S.toks) => //.
  proc (H0C.CQ.n <= Cnt.c0 + tthr * Cnt.cs /\ size H0C.ER.ts <= tthr * Cnt.cs
        /\ tokinv S.toks) => //.
  + by move=> &hr /> *; smt().
  + by proc; sp; ecall (o1_ec H0C.CQ.n (size H0C.ER.ts)); auto => /#.
  + by proc; sp; ecall (o2_ec H0C.CQ.n (size H0C.ER.ts)); auto => /#.
  + by proc; sp; ecall (o3_ec H0C.CQ.n (size H0C.ER.ts)); auto => /#.
  + by proc; sp; ecall (h0_ec H0C.CQ.n (size H0C.ER.ts)); auto => /#.
  + by proc; inline *; auto.
  + by proc; inline *; auto.
auto; call (_ : true); inline *; auto => />; smt(mem_empty).
qed.

(* Answering corrupt first messages with the extractable simulator *)
lemma ext_hop &m :
  `|Pr[H0C.EG(DE(A)).main(false) @ &m : res] - Pr[H0C.EG(DE(A)).main(true) @ &m : res]|
  <= 8%r * lx%r * (qx + lx)%r * sqrt (2%r * p_max dcmt).
proof.
apply (H0C.ext_sim (DE(A)) &m qx lx _ _ de_cnt).
+ by rewrite /qx; smt(ge0_qh0 ge0_qsig thr_range).
by rewrite /lx; smt(ge0_qsig thr_range).
qed.

(* Accepted corrupt openings match their extractions *)
lemma ext_bad &m :
  Pr[H0C.EG(DE(A)).main(true) @ &m : H0C.extbad H0C.ER.ts H0C.ER.xs H0C.ER.cks]
  <= 8%r * lx%r * (qx + 1)%r * sqrt (2%r * p_max dcmt)
     + (40%r * exp 1%r ^ 2 * (qx + lx + 1)%r ^ 3 + 2%r) * p_max dcmt.
proof.
apply (H0C.ext_sound (DE(A)) &m qx lx _ _ de_cnt).
+ by rewrite /qx; smt(ge0_qh0 ge0_qsig thr_range).
by rewrite /lx; smt(ge0_qsig thr_range).
qed.

(* The flagged lazy game is close to the extraction game without extraction failures *)
lemma ga_ext &m :
  Pr[H0H.LCG(BA(A)).main(true) @ &m : res /\ !Bd.b1 /\ !Bd.b2 /\ !Bd.b3]
  <= Pr[H0C.EG(DE(A)).main(true) @ &m : res /\ !H0C.extbad H0C.ER.ts H0C.ER.xs H0C.ER.cks]
     + 8%r * lx%r * (qx + lx)%r * sqrt (2%r * p_max dcmt)
     + (8%r * lx%r * (qx + 1)%r * sqrt (2%r * p_max dcmt)
        + (40%r * exp 1%r ^ 2 * (qx + lx + 1)%r ^ 3 + 2%r) * p_max dcmt).
proof.
rewrite (ga_ge &m).
have h1 := ext_hop &m.
have h2 := ext_bad &m.
have h3 : Pr[H0C.EG(DE(A)).main(true) @ &m : res]
       <= Pr[H0C.EG(DE(A)).main(true) @ &m : res /\ !H0C.extbad H0C.ER.ts H0C.ER.xs H0C.ER.cks]
          + Pr[H0C.EG(DE(A)).main(true) @ &m : H0C.extbad H0C.ER.ts H0C.ER.xs H0C.ER.cks].
+ rewrite Pr[mu_split (H0C.extbad H0C.ER.ts H0C.ER.xs H0C.ER.cks)].
  have : Pr[H0C.EG(DE(A)).main(true) @ &m : res /\ H0C.extbad H0C.ER.ts H0C.ER.xs H0C.ER.cks]
      <= Pr[H0C.EG(DE(A)).main(true) @ &m : H0C.extbad H0C.ER.ts H0C.ER.xs H0C.ER.cks].
  - by rewrite Pr[mu_sub].
  smt().
smt().
qed.

end section ExtHop.
