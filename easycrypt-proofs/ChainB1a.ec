require import AllCore Int List Distr DList FMap FSet Real RealExp Finite StdOrder StdBigop.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption.
require import Protocol Notions Privacy Extract FinEnum ChainBase ChainGame ChainCol ChainSim.
require import ChainDead ChainLazy ChainFlag ChainGA.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

(* ---------- the first flag: an accepted check against an inconsistent token ----------

   The run is replayed by an adversary against the lazy commitment oracle that logs, at each
   honest check, the point of the check together with every unopened token of the checked
   party, reveals the unopened tokens at the end, and outputs the first flag together with the
   absence of a logged point that equals the opening of its token (Ept).  The lazy commitments
   are then exchanged for eager ones (o2h), where the first flag without Ept gives a collision of
   H0, and Ept itself is bounded in the lazy game, where the nonces of the logged tokens are
   sampled after their logged checks. *)

module Lg1 = {
  var log : (h0in * int) list
  var sec : (int, vec * row) fmap
  var ept : bool
}.

(* The signing oracles of the lazy game with flags, with the honest checks logged and the
   revealed nonces recorded *)
module BXO (O : H0H.LC_i) : SOr = {
  proc h0any = SOA(O).h0any

  proc o1 = SOA(O).o1

  proc o2(u : int, T : committee, cs : cmt list) : row option = {
    var out, tok, d, s;
    out <- None;
    if (u \in S.toks) {
      tok <- oget S.toks.[u];
      if (ok2 tok T cs) {
        d <- H1O.QRO.fh (e1 S.t tok.`tk_msg T cs);
        s <@ O.reveal(u);
        Lg1.sec.[u] <- s;
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
        d <- H1O.QRO.fh (e1 S.t tok.`tk_msg T cs);
        if (d = tok.`tk_dig) {
          Bd.b3 <- Bd.b3 \/ cs <> (oget S.req.[u]).`3;
          okk <- true;
          k <- 0;
          while (k < size T) {
            if (!(nth 0 T k \in S.cs)) {
              Lg1.log <- Lg1.log ++ map (fun w => ((((S.t, tok.`tk_msg), toidx (nth 0 T k)), nth witness ws k), w))
                           (filter (fun w => (oget S.toks.[w]).`tk_phase = 1 /\ (oget S.toks.[w]).`tk_i = nth 0 T k)
                                   (elems (fdom S.toks)));
            }
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

module GameX (A : Adv) (O : H0H.LC_i) = {
  proc run() : bool = {
    var mu, sg, ok, sks, sds;
    S.cs <@ A(CntH(HOL(O)), CntO(BXO(O))).corrupt();
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
    (mu, sg) <@ A(CntH(HOL(O)), CntO(BXO(O))).forge(S.t, sks, sds);
    ok <- verify (hcof HCO.QRO.fh) S.t mu sg /\ admc S.cs;
    return win4 S.cs S.lo mu ok;
  }
}.

(* The final reveals of the unopened tokens, counted with the signing queries *)
module Fin (O : H0H.LC_i) = {
  proc rev(u : int) : unit = {
    var s;
    Cnt.cs <- Cnt.cs + 1;
    s <@ O.reveal(u);
    Lg1.sec.[u] <- s;
  }
}.

(* A logged point equal to the opening of its token *)
op eptof (log : (h0in * int) list) (sec : (int, vec * row) fmap) : bool =
  has (fun (e : h0in * int) => e.`2 \in sec /\ popn (oget sec.[e.`2]) = e.`1.`2) log.

module BBX (A : Adv) (O : H0H.LC_i) = {
  proc main() : bool = {
    var b, us, k;
    H0C.QRO.init();
    H1O.QRO.init();
    HCO.QRO.init();
    Lg1.log <- [];
    Lg1.sec <- empty;
    Lg1.ept <- false;
    b <@ GameX(A, O).run();
    us <- filter (fun u => (oget S.toks.[u]).`tk_phase = 1) (elems (fdom S.toks));
    k <- 0;
    while (k < size us) {
      Fin(O).rev(nth 0 us k);
      k <- k + 1;
    }
    Lg1.ept <- eptof Lg1.log Lg1.sec;
    return Bd.b1 /\ !Lg1.ept;
  }
}.

(* The queries to H0 and the revealed nonces are bounded by the signing queries *)
op [opaque] qinv (n c0 cs : int) (sv : (int, vec * row) fmap) (toks : (int, token) fmap) : bool =
  0 <= cs /\ n <= c0 + tthr * cs /\ (forall u, u \in sv => u \in toks) /\ card (fdom toks) <= cs
  /\ (forall u, u \in toks => (oget toks.[u]).`tk_phase = 2 => size (oget toks.[u]).`tk_T = tthr).

lemma lch_q (n0 : int) :
  hoare [H0H.LC.h : H0H.CQ.n = n0 /\ (forall u, u \in H0H.LC.sv => u \in S.toks) ==>
                    H0H.CQ.n = n0 + 1 /\ (forall u, u \in H0H.LC.sv => u \in S.toks)].
proof. by proc; inline *; sp; if; [sp; if; auto | auto]. qed.

lemma h0_q : hoare [CntH(HOL(H0H.LC)).h0 : qinv H0H.CQ.n Cnt.c0 Cnt.cs H0H.LC.sv S.toks ==> qinv H0H.CQ.n Cnt.c0 Cnt.cs H0H.LC.sv S.toks].
proof.
proc; inline HOL(H0H.LC).h0; sp; if; first by auto; rewrite /qinv => &h />; smt().
wp; ecall (lch_q H0H.CQ.n); auto; rewrite /qinv => &h />; smt(thr_range).
qed.

lemma h1_q : hoare [CntH(HOL(H0H.LC)).h1 : qinv H0H.CQ.n Cnt.c0 Cnt.cs H0H.LC.sv S.toks ==> qinv H0H.CQ.n Cnt.c0 Cnt.cs H0H.LC.sv S.toks].
proof. by proc; inline *; auto. qed.

lemma hc_q : hoare [CntH(HOL(H0H.LC)).hc : qinv H0H.CQ.n Cnt.c0 Cnt.cs H0H.LC.sv S.toks ==> qinv H0H.CQ.n Cnt.c0 Cnt.cs H0H.LC.sv S.toks].
proof. by proc; inline *; auto. qed.

lemma o1_q : hoare [CntO(BXO(H0H.LC)).o1 : qinv H0H.CQ.n Cnt.c0 Cnt.cs H0H.LC.sv S.toks ==> qinv H0H.CQ.n Cnt.c0 Cnt.cs H0H.LC.sv S.toks].
proof.
proc; inline BXO(H0H.LC).o1; sp; if; last by auto; rewrite /qinv => &h />; smt(thr_range).
inline *; sp; if.
+ sp; if; auto; rewrite /qinv => &h /> *; rewrite fdom_set fcardU1; smt(mem_set get_setE thr_range).
sp; if; auto; rewrite /qinv => &h /> *; rewrite fdom_set fcardU1; smt(mem_set get_setE thr_range).
qed.

lemma o2_q : hoare [CntO(BXO(H0H.LC)).o2 : qinv H0H.CQ.n Cnt.c0 Cnt.cs H0H.LC.sv S.toks ==> qinv H0H.CQ.n Cnt.c0 Cnt.cs H0H.LC.sv S.toks].
proof.
proc; inline BXO(H0H.LC).o2; sp; if; last by auto; rewrite /qinv => &h />; smt(thr_range).
sp; if; last by auto; rewrite /qinv => &h />; smt(thr_range).
inline *; sp; if; auto; rewrite /qinv => &h /> *;
  rewrite fdom_set fcardU1 ?mem_fdom; smt(mem_set get_setE thr_range).
qed.

lemma qinv_mono n n' c0 cs sv toks : n' <= n => qinv n c0 cs sv toks => qinv n' c0 cs sv toks.
proof. by rewrite /qinv; smt(). qed.

lemma h0any_q (n0 : int) :
  hoare [SOA(H0H.LC).h0any : H0H.CQ.n = n0 /\ (forall u, u \in H0H.LC.sv => u \in S.toks) ==>
                             H0H.CQ.n <= n0 + 1 /\ (forall u, u \in H0H.LC.sv => u \in S.toks)].
proof. by proc; sp; if; [auto => /> /# | wp; ecall (lch_q H0H.CQ.n); auto => /> /#]. qed.

lemma o3_q : hoare [CntO(BXO(H0H.LC)).o3 : qinv H0H.CQ.n Cnt.c0 Cnt.cs H0H.LC.sv S.toks ==> qinv H0H.CQ.n Cnt.c0 Cnt.cs H0H.LC.sv S.toks].
proof.
proc; inline BXO(H0H.LC).o3; sp; if; last by auto; rewrite /qinv => &h />; smt(thr_range).
sp; if; last by auto; rewrite /qinv => &h />; smt(thr_range).
sp; if; last by auto; rewrite /qinv => &h />; smt(thr_range).
seq 3 : (qinv (H0H.CQ.n - k) Cnt.c0 (Cnt.cs - 1) H0H.LC.sv S.toks /\ k = 0 /\ size T0 = tthr
         /\ u0 \in S.toks /\ tok = oget S.toks.[u0] /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T).
+ by auto; rewrite /qinv => &h />; smt(thr_range).
seq 1 : (qinv (H0H.CQ.n - k) Cnt.c0 (Cnt.cs - 1) H0H.LC.sv S.toks /\ 0 <= k <= size T0 /\ size T0 = tthr
         /\ u0 \in S.toks /\ tok = oget S.toks.[u0] /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T).
+ while (qinv (H0H.CQ.n - k) Cnt.c0 (Cnt.cs - 1) H0H.LC.sv S.toks /\ 0 <= k <= size T0 /\ size T0 = tthr
         /\ u0 \in S.toks /\ tok = oget S.toks.[u0] /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T).
  - wp; ecall (h0any_q H0H.CQ.n); auto => /> &h hq hk0 hk1 hsz hu hph hk.
    split; first by move: hq; rewrite /qinv => /#.
    move=> hsv n hn; split; last smt().
    by apply (qinv_mono (H0H.CQ.n{h} - k{h})); first smt().
  by auto => />.
if; last by auto; rewrite /qinv => &h /> /#.
seq 5 : (qinv (H0H.CQ.n - size T0) Cnt.c0 (Cnt.cs - 1) H0H.LC.sv S.toks /\ size T0 = tthr
         /\ u0 \in S.toks /\ tok = oget S.toks.[u0] /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T).
+ auto => /> &h hq hk0 hk1 hsz hu hph _.
  by apply (qinv_mono (H0H.CQ.n{h} - k{h})); first smt().
seq 1 : (qinv (H0H.CQ.n - size T0) Cnt.c0 (Cnt.cs - 1) H0H.LC.sv S.toks /\ size T0 = tthr
         /\ u0 \in S.toks /\ tok = oget S.toks.[u0] /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T).
+ by while (qinv (H0H.CQ.n - size T0) Cnt.c0 (Cnt.cs - 1) H0H.LC.sv S.toks /\ size T0 = tthr
         /\ u0 \in S.toks /\ tok = oget S.toks.[u0] /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T); auto.
by sp; if; [auto | if; auto] => /> &h; rewrite /qinv => *;
   rewrite fdom_set fcardU1 ?mem_fdom; smt(mem_set get_setE thr_range).
qed.

section B1a.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -Fz, -Bd, -Lg1, -H0H.QRO, -H0C.QRO, -H1O.QRO,
                         -HCO.QRO, -H0H.LC, -H0H.CQ}.

(* The logging replay has the first flag of the lazy game with flags *)
lemma ga_bbx &m :
  Pr[H0H.LCG(BA(A)).main(true) @ &m : Bd.b1] = Pr[H0H.LCG(BBX(A)).main(true) @ &m : Bd.b1].
proof.
byequiv => //; proc.
inline BA(A, H0H.LC).main BBX(A, H0H.LC).main GameA(A, H0H.LC).run GameX(A, H0H.LC).run.
wp.
while{2} (true) (size us{2} - k{2}).
+ move=> _ z; inline *; wp; sp; if; auto; smt(H0H.dsec_ll).
wp.
call (_ : ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt,
            glob Fz, glob Bd, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H1O.QRO,
            glob HCO.QRO}).
+ by proc; inline *; sim.
+ by proc; inline *; sim.
+ by proc; inline *; sim.
+ by proc; inline *; sim.
+ by proc; inline *; sim.
+ by proc; inline *; sim.
by auto; call (_ : true); inline *; auto => /> /#.
qed.

declare axiom A_bnd (H <: HOr {-A, -Cnt}) (O <: SOr {-A, -Cnt}) :
  hoare [A(CntH(H), CntO(O)).forge : Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 ==>
         Cnt.c0 <= qh0 /\ Cnt.c1 <= qh1 /\ Cnt.cc <= qhc /\ Cnt.cs <= qsig].

declare axiom reg_open :
  forall (w : row), mu (dnonce `*` dnoiser) (fun (s : vec * row) => rndc (commit s.`1 s.`2) = w) <= pw.

local lemma forge_q :
  hoare [A(CntH(HOL(H0H.LC)), CntO(BXO(H0H.LC))).forge :
    qinv H0H.CQ.n Cnt.c0 Cnt.cs H0H.LC.sv S.toks
    /\ Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 ==>
    qinv H0H.CQ.n Cnt.c0 Cnt.cs H0H.LC.sv S.toks /\ Cnt.c0 <= qh0 /\ Cnt.cs <= qsig].
proof.
conseq (A_bnd (HOL(H0H.LC)) (BXO(H0H.LC)))
       (_ : qinv H0H.CQ.n Cnt.c0 Cnt.cs H0H.LC.sv S.toks ==> qinv H0H.CQ.n Cnt.c0 Cnt.cs H0H.LC.sv S.toks)
       => //.
proc (qinv H0H.CQ.n Cnt.c0 Cnt.cs H0H.LC.sv S.toks) => //.
+ exact o1_q.
+ exact o2_q.
+ exact o3_q.
+ exact h0_q.
+ exact h1_q.
+ exact hc_q.
qed.

(* The replay asks H0 at most qh0 + tthr qsig times and reveals at most qsig nonces *)
local lemma bbx_q :
  hoare [BBX(A, H0H.LC).main : H0H.CQ.n = 0 /\ H0H.LC.sv = empty ==>
         H0H.CQ.n <= qh0 + tthr * qsig /\ card (fdom H0H.LC.sv) <= qsig].
proof.
proc; inline GameX(A, H0H.LC).run.
wp.
while (H0H.CQ.n <= qh0 + tthr * qsig /\ (forall u, u \in H0H.LC.sv => u \in S.toks)
       /\ card (fdom S.toks) <= qsig /\ (forall i, 0 <= i < size us => nth 0 us i \in S.toks) /\ 0 <= k).
+ by inline *; sp; if; auto => />; smt(mem_set).
wp.
call forge_q.
auto; call (_ : true); inline *; auto => /> *;
  (split; first by rewrite /qinv fdom0 fcards0 /=; smt(mem_empty));
  (move=> hinit c0 cs toks n sv hq hc0 hcs; split;
   [ move: hq; rewrite /qinv => -[#] h0 h1 h2 h3 _; do !split;
       [smt(thr_range) | exact h2 | smt() | move=> i hi0 hi1; smt(mem_nth List.mem_filter memE mem_fdom)]
   | move=> sv' k hk hn hsv hct _ _; apply (StdOrder.IntOrder.ler_trans (card (fdom toks)));
       [apply subset_leq_fcard; apply/subsetP => u; rewrite !mem_fdom; apply hsv | exact hct]]).
qed.

(* The lazy commitments are hard to tell from eager ones in the replay *)
lemma bbx_o2h &m :
  `|Pr[H0H.LCG(BBX(A)).main(true) @ &m : res] - Pr[H0H.LCG(BBX(A)).main(false) @ &m : res]|
  <= 2%r * (qh0 + tthr * qsig)%r * sqrt (qsig%r * pw) + (qsig * qsig)%r * pw.
proof.
apply (H0H.o2h_lazy (BBX(A)) &m (qh0 + tthr * qsig) qsig pw _ _ _ _ bbx_q).
+ smt(ge0_qh0 ge0_qsig thr_range).
+ exact ge0_qsig.
+ by have := reg_open witness; smt(mu_bounded).
exact reg_open.
qed.

end section B1a.
