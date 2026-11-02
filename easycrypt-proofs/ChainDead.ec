require import AllCore Int List Distr DList FMap FSet Real RealExp Finite StdOrder.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption.
require import Protocol Notions Privacy Extract FinEnum ChainBase ChainGame ChainCol ChainSim.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

module SOFt (H0h : H0H.QRO_i) (H1 : H1O.QRO_i) : SOr = {
  proc o1 = SOF(MPI, H0h, H1).o1
  proc o2 = SOF(MPI, H0h, H1).o2

  proc o3(u : int, T : committee, cs : cmt list, ws : row list) : vec option = {
    var out, tok, d, k, okk, y, c, z, mkh, mkc, j, v, ys, f;
    out <- None;
    if (u \in S.toks) {
      tok <- oget S.toks.[u];
      if (tok.`tk_phase = 2 /\ T = tok.`tk_T /\ size cs = size T /\ size ws = size T
          /\ nth witness ws (index tok.`tk_i T) = tok.`tk_wbar) {
        d <@ SOF(MPI, H0h, H1).h1hon(e1 S.t tok.`tk_msg T cs);
        if (d = tok.`tk_dig) {
          okk <- true;
          k <- 0;
          while (k < size T) {
            y <@ SOF(MPI, H0h, H1).h0any((((S.t, tok.`tk_msg), toidx (nth 0 T k)), nth witness ws k));
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

module GameFt (A : Adv) (H0h : H0H.QRO_i) (H1 : H1O.QRO_i) = {
  proc run() : bool = {
    var mu, sg, ok, sks, sds;
    S.cs <@ A(CntH(HOF(H0h, H1)), CntO(SOFt(H0h, H1))).corrupt();
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
    Fz.fz <- empty;
    Cnt.c0 <- 0;
    Cnt.c1 <- 0;
    Cnt.cc <- 0;
    Cnt.cs <- 0;
    sks <- fun j => if j \in S.cs then shr S.s S.p j else RqVec.Vector.zerov;
    sds <- fun (ab : pidx * pidx) =>
             if hpair S.cs (PIdx.val ab.`1) (PIdx.val ab.`2) then witness else S.sdc ab;
    (mu, sg) <@ A(CntH(HOF(H0h, H1)), CntO(SOFt(H0h, H1))).forge(S.t, sks, sds);
    ok <- verify (hcof HCO.QRO.fh) S.t mu sg /\ admc S.cs;
    return win4 S.cs S.lo mu ok;
  }
}.

module G1t (A : Adv) = {
  proc main() : bool = {
    var b;
    H0H.QRO.init();
    H0C.QRO.init();
    H1O.QRO.init();
    HCO.QRO.init();
    b <@ GameFt(A, H0H.QRO, H1O.QRO).run();
    return b;
  }
}.

section DeadHop.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -Fz, -H0H.QRO, -H0C.QRO, -H1O.QRO, -HCO.QRO,
                          -H0H.CQ, -H1O.CQ}.

(* Mask values are lossless *)
lemma mpi_ll : islossless MPI.f.
proof. by proc; sp; if; auto => />; smt(dvec_ll). qed.

(* Unused masks leave third rounds unchanged *)
equiv o3_dead :
  SOFs(H0H.QRO, H1O.QRO).o3 ~ SOFt(H0H.QRO, H1O.QRO).o3 :
  ={u, T, cs, ws} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr,
                       Lg.l0, Lg.l1, Fz.fz, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}
  ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr,
                  Lg.l0, Lg.l1, Fz.fz, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}.
proof.
proc; sp; if => //.
sp; if => //.
seq 1 1 : (={u, T, cs, ws, tok, d, out} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req,
             S.ctr, S.lo, S.lr, Lg.l0, Lg.l1, Fz.fz, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh,
             HCO.QRO.fh}); first by sim.
if => //.
seq 3 3 : (={u, T, cs, ws, tok, d, out, okk} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks,
             S.req, S.ctr, S.lo, S.lr, Lg.l0, Lg.l1, Fz.fz, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh,
             HCO.QRO.fh}); first by sim.
if => //.
seq 6 6 : (={u, T, cs, ws, tok, d, out, okk, c, ys, mkc} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc,
             S.toks, S.req, S.ctr, S.lo, S.lr, Lg.l0, Lg.l1, Fz.fz, H0H.QRO.fh, H0C.QRO.fh,
             H1O.QRO.fh, HCO.QRO.fh}).
+ while (={k, u, T, cs, ws, tok, d, out, okk, c, ys, mkc} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc,
          S.toks, S.req, S.ctr, S.lo, S.lr, Lg.l0, Lg.l1, Fz.fz, H0H.QRO.fh, H0C.QRO.fh,
          H1O.QRO.fh, HCO.QRO.fh}); last by auto.
  seq 1 1 : (={j, k, u, T, cs, ws, tok, d, out, okk, c, ys, mkc} /\ ={S.cs, S.s, S.e, S.p, S.t,
               S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, Lg.l0, Lg.l1, Fz.fz, H0H.QRO.fh,
               H0C.QRO.fh, H1O.QRO.fh, HCO.QRO.fh}); first by auto.
  if => //; last by auto.
  if => //; last by auto.
  by wp; call{1} mpi_ll; auto.
sp; if => //; first by auto.
if => //; last by auto.
by wp; rnd; auto.
qed.

(* Dropping the unused masks keeps the game *)
lemma g1s_g1t &m : Pr[G1s(A).main() @ &m : res] = Pr[G1t(A).main() @ &m : res].
proof.
byequiv => //; proc; inline GameFs(A, H0H.QRO, H1O.QRO).run GameFt(A, H0H.QRO, H1O.QRO).run.
wp.
call (_ : ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, Lg.l0, Lg.l1,
            Fz.fz, Cnt.c0, Cnt.c1, Cnt.cc, Cnt.cs, H0H.QRO.fh, H0C.QRO.fh, H1O.QRO.fh,
            HCO.QRO.fh}).
+ by proc; inline *; sim.
+ by proc; inline *; sim.
+ by proc; wp; call o3_dead; auto.
+ by proc; inline *; auto.
+ by proc; inline *; auto.
+ by proc; inline *; auto.
auto; call (_ : true); inline *; auto.
qed.

end section DeadHop.
