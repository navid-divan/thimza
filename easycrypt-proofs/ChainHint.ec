require import AllCore Int List Distr DList FMap FSet Real RealExp Finite StdOrder.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption.
require import Protocol Notions Privacy Extract FinEnum ChainBase ChainGame ChainCol ChainSim.
require import ChainDead ChainLazy ChainFlag ChainExt ChainRep ChainProg.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.


(* The values that the game with shares stores for each response, kept as a ghost *)
module Rg = {
  var fz : (request * int, vec * vec) fmap
}.

module SOH : SOr = {
  proc o1 = SOA(H0H.LC).o1
  proc o2 = SOP.o2

  proc o3(u : int, T : committee, cs : cmt list, ws : row list) : vec option = {
    var out, tok, d, k, okk, y, c, z, mkh, mkc, j, v, ys, f, dzk, g;
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
            g <- (if Rx.lop.[oget S.req.[u]] = Some u then RqVec.Vector.zerov else tok.`tk_r) + mkc;
            Rp.bH <- Rp.bH \/ (oget S.req.[u], tok.`tk_i) \in S.lr
                   \/ (oget S.req.[u] \in Rp.cV /\ c <> oget Rp.cV.[oget S.req.[u]])
                   \/ (ys = [] /\ !(oget S.req.[u] \in Rp.cV))
                   \/ (oget S.req.[u] \in Rx.lop /\ oget Rx.lop.[oget S.req.[u]] <> u
                       /\ (oget S.toks.[oget Rx.lop.[oget S.req.[u]]]).`tk_i = tok.`tk_i)
                   \/ T <> (oget S.req.[u]).`2
                   \/ (ys = [] /\ !((oget S.req.[u], tok.`tk_i) \in S.lr)
                       /\ !okclose Rx.lop Rp.sV Rp.cV S.toks Rg.fz Rp.cz Rh.dz S.cs
                                    (oget S.req.[u]) T tok.`tk_i dzk);
            if ((oget S.req.[u], tok.`tk_i) \in S.lr) {
              z <$ dvec;
            } else {
              if (ys <> []) {
                z <$ dvec;
              } else {
                if (oget S.req.[u] \in Rp.cV) {
                  z <- ((oget Rp.cV.[oget S.req.[u]]) ** S.s + (oget Rp.sV.[oget S.req.[u]]).`1
                        - vmap (fun j => (Rq.( * ) (oget Rp.cV.[oget S.req.[u]]) (lam_of T j))
                                         ** shr S.s S.p j) (corrupted T S.cs))
                       + g + vmap (fun a => (oget Fz.fz.[(oget S.req.[u], a)]).`2
                                            - (oget Fz.fz.[(oget S.req.[u], a)]).`1)
                                  (filter (fun a => a <> tok.`tk_i) (honest T S.cs));
                } else {
                  z <- RqVec.Vector.zerov;
                }
              }
              Fz.fz.[(oget S.req.[u], tok.`tk_i)] <- (z, g);
              Rg.fz.[(oget S.req.[u], tok.`tk_i)] <- (z, f);
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

module GH (A : Adv) = {
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
    S.cs <@ A(CntH(HOP), CntO(SOH)).corrupt();
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
    Rg.fz <- empty;
    Cnt.c0 <- 0;
    Cnt.c1 <- 0;
    Cnt.cc <- 0;
    Cnt.cs <- 0;
    sks <- fun j => if j \in S.cs then shr S.s S.p j else RqVec.Vector.zerov;
    sds <- fun (ab : pidx * pidx) =>
             if hpair S.cs (PIdx.val ab.`1) (PIdx.val ab.`2) then witness else S.sdc ab;
    (mu, sg) <@ A(CntH(HOP), CntO(SOH)).forge(S.t, sks, sds);
    cv <- Rp.fhp (liftw (rndw (mulA mA sg.`2 - rowZ sg.`1 (liftt S.t)) + sg.`3), (S.t, mu));
    ok <- (cv = sg.`1 /\ inbnd sg.`2 sg.`3) /\ admc S.cs;
    return win4 S.cs S.lo mu ok /\ !Bd.b1 /\ !Bd.b2 /\ !Bd.b3
           /\ !H0C.extbad H0C.ER.ts H0C.ER.xs H0C.ER.cks;
  }
}.

(* A sum that selects one member of a list without repetition *)
lemma vmap_one (H : int list) (p : int) (r : vec) :
  uniq H => p \in H => vmap (fun a => if a = p then r else RqVec.Vector.zerov) H = r.
proof.
elim: H => [| a H ih] //= [ha hu] hp.
rewrite vmap_cons /=.
case: (a = p) => [hap | hap].
+ have -> : vmap (fun a0 => if a0 = p then r else RqVec.Vector.zerov) H
          = vmap (fun _ => RqVec.Vector.zerov) H.
  - by apply vmap_eq => x hx /=; smt().
  by rewrite vmap0 RqVec.Vector.ZModule.addr0.
by rewrite ih 1:// 1:/# RqVec.Vector.ZModule.add0r.
qed.

(* Honest Lagrange terms close with the corrupt ones to the secret *)
lemma honest_lag (T : committee) (C : corrset) (c : rq) (s : vec) (pp : int -> vec) :
  wf_nodes T =>
  vmap (fun a => (Rq.( * ) c (lam_of T a)) ** shr s pp a) (honest T C)
  = c ** s - vmap (fun j => (Rq.( * ) c (lam_of T j)) ** shr s pp j) (corrupted T C).
proof.
move=> hwf.
pose K := fun a => (Rq.( * ) c (lam_of T a)) ** shr s pp a.
have hK : vmap K (honest T C) + vmap K (corrupted T C) = c ** s.
+ rewrite honest_corrupted_split.
  have -> : vmap K T = vmap (fun j => c ** (lam_of T j ** shr s pp j)) T.
  - by apply vmap_eq => j _; rewrite /K vscaleA.
  rewrite -scalev_vmap (shr_recons T (lam_of T) s pp); last done.
  by apply lam_of_recons => //; smt(thr_range).
have -> : vmap (fun a => (Rq.( * ) c (lam_of T a)) ** shr s pp a) (honest T C)
        = vmap K (honest T C) by done.
rewrite -hK; smt(RqVec.Vector.ZModule.addrK).
qed.

(* Regrouping of five summands *)
lemma reorg5 (a g b x y : vec) : a + g + b + (x + y) = a + b + x + g + y.
proof. smt(RqVec.Vector.ZModule.addrA RqVec.Vector.ZModule.addrC). qed.

(* Regrouping of a difference *)
lemma reorg3 (s c r : vec) : s - c + r = s + r - c.
proof. smt(RqVec.Vector.ZModule.addrA RqVec.Vector.ZModule.addrC). qed.

(* Regrouping of a share term *)
lemma reorg4 (k f d z : vec) : k + f + d - z = k + d + (f - z).
proof. smt(RqVec.Vector.ZModule.addrA RqVec.Vector.ZModule.addrC). qed.

(* The last honest response computed from a hint equals the one computed from the shares *)
lemma close_hint (T : committee) (C : corrset) (i p : int) (c : rq) (s : vec) (pp : int -> vec)
                 (r : vec) (f1 f2 z : int -> vec) (fi gi : vec) :
  wf_nodes T => uniq (honest T C) => i \in honest T C => p \in honest T C =>
  (forall a, a \in honest T C => a <> i =>
     f1 a = (Rq.( * ) c (lam_of T a)) ** shr s pp a + f2 a
            + (if a = p then r else RqVec.Vector.zerov)) =>
  fi = (Rq.( * ) c (lam_of T i)) ** shr s pp i + gi + (if i = p then r else RqVec.Vector.zerov) =>
  fi + vmap (fun a => f1 a - z a) (filter (fun a => a <> i) (honest T C))
  = (c ** s + r - vmap (fun j => (Rq.( * ) c (lam_of T j)) ** shr s pp j) (corrupted T C))
    + gi + vmap (fun a => f2 a - z a) (filter (fun a => a <> i) (honest T C)).
proof.
move=> hwf hu hi hp hf ->.
have e1 : vmap (fun a => f1 a - z a) (filter (fun a => a <> i) (honest T C))
        = vmap (fun a => (Rq.( * ) c (lam_of T a)) ** shr s pp a
                         + (if a = p then r else RqVec.Vector.zerov))
               (filter (fun a => a <> i) (honest T C))
          + vmap (fun a => f2 a - z a) (filter (fun a => a <> i) (honest T C)).
+ rewrite -vmap_split; apply vmap_eq => a; rewrite mem_filter => -[hai ha] /=.
  by rewrite (hf a ha hai) reorg4.
have eK := honest_lag T C c s pp hwf.
have eD := vmap_one (honest T C) p r hu hp.
have /= eR := vmap_rem1 (fun a => (Rq.( * ) c (lam_of T a)) ** shr s pp a
                               + (if a = p then r else RqVec.Vector.zerov)) (honest T C) i hu hi.
have /= eS := vmap_split (fun a => (Rq.( * ) c (lam_of T a)) ** shr s pp a)
                         (fun a => if a = p then r else RqVec.Vector.zerov) (honest T C).
rewrite e1 reorg5.
congr; congr.
by rewrite -eR eS eK eD reorg3.
qed.

(* The ghost values of the game with shares are related to the stored values of the hint game *)
op [opaque] relh (fz gz : (request * int, vec * vec) fmap) (cz : (request * int, rq) fmap)
        (dz : (request * int, vec) fmap) (s : vec) (p : int -> vec) : bool =
  (forall k, k \in fz <=> k \in gz)
  /\ (forall k, k \in fz => k \in cz /\ k \in dz /\ (oget gz.[k]).`1 = (oget fz.[k]).`1
        /\ (oget gz.[k]).`2 = (Rq.( * ) (oget cz.[k]) (lam_of k.`1.`2 k.`2)) ** shr s p k.`2
                              + (oget fz.[k]).`2 + oget dz.[k]).

(* First rounds terminate and keep the flag *)
lemma o1_bh : phoare [CntO(SOP).o1 : Rp.bH ==> Rp.bH] = 1%r.
proof.
proc; inline *; sp; if; last by auto.
by sp; if; sp; if; auto => />; smt(dcmt_ll dnp_ll).
qed.

(* First rounds of the hint game terminate and keep the flag *)
lemma o1_bhh : phoare [CntO(SOH).o1 : Rp.bH ==> Rp.bH] = 1%r.
proof.
proc; inline *; sp; if; last by auto.
by sp; if; sp; if; auto => />; smt(dcmt_ll dnp_ll).
qed.

(* Checks terminate *)
lemma chk_ll : islossless SOE(H0C.ER).chk.
proof.
proc; if.
+ by if; inline *; auto.
by inline *; sp; if; [sp; if; auto => />; smt(dcmt_ll) | auto].
qed.

(* Checks keep the flag *)
lemma chk_mono : hoare [SOE(H0C.ER).chk : Rp.bH ==> Rp.bH].
proof.
proc; if.
+ by if; inline *; auto.
by inline *; sp; if; [sp; if; auto | auto].
qed.

(* Submissions terminate *)
lemma subm_ll : islossless SOR(HCO.CQ, HCO.Rep).subm.
proof.
proc; sp.
while true (size V.`2 - k); last by auto => /> /#.
move=> z; wp; if; last by auto => /> /#.
by inline *; auto => /> /#.
qed.

(* Submissions keep the flag *)
lemma subm_mono : hoare [SOR(HCO.CQ, HCO.Rep).subm : Rp.bH ==> Rp.bH].
proof. by proc; sp; while (Rp.bH); [wp; if; [inline *; auto | auto] | auto]. qed.

(* Second rounds terminate *)
lemma sop_o2_ll : islossless SOP.o2.
proof.
proc; sp; if => //.
sp; if => //.
sp; if.
+ seq 1 : true => //; first by call subm_ll.
  by sp; if; auto => />; smt(dnp_ll dchal_ll).
by inline *; sp; if; auto => />; smt(dnp_ll).
qed.

(* Second rounds keep the flag *)
lemma sop_o2_mono : hoare [SOP.o2 : Rp.bH ==> Rp.bH].
proof.
proc; sp; if => //.
sp; if => //.
sp; if.
+ seq 1 : (Rp.bH); first by call subm_mono.
  by sp; if; auto => /> /#.
by inline *; sp; if; auto.
qed.

(* Third rounds of the game with shares terminate *)
lemma sop_o3_ll : islossless SOP.o3.
proof.
proc; sp; if => //.
sp; if => //.
seq 1 : true => //; first by auto.
if => //.
seq 4 : true => //; first by auto.
seq 1 : true => //.
+ while true (size T - k); last by auto => /> /#.
  by move=> z; wp; call chk_ll; auto => /> /#.
if => //.
seq 6 : true => //.
+ while true (size T - k); last by auto => /> /#.
  by move=> z; auto => /> /#.
sp; if; first by auto.
wp; if; last by auto.
by wp; rnd; auto => />; smt(dvec_ll).
qed.

(* Third rounds of the game with shares keep the flag *)
lemma sop_o3_mono : hoare [SOP.o3 : Rp.bH ==> Rp.bH].
proof.
proc; sp; if => //.
sp; if => //.
seq 1 : (Rp.bH); first by auto.
if => //.
seq 4 : (Rp.bH); first by auto.
seq 1 : (Rp.bH).
+ by while (Rp.bH); [wp; call chk_mono; auto | auto].
if => //.
seq 6 : (Rp.bH); first by while (Rp.bH); auto.
by sp; if; [auto => /> /# | if; auto => /> /#].
qed.

(* Third rounds of the hint game terminate *)
lemma soh_o3_ll : islossless SOH.o3.
proof.
proc; sp; if => //.
sp; if => //.
seq 1 : true => //; first by auto.
if => //.
seq 4 : true => //; first by auto.
seq 1 : true => //.
+ while true (size T - k); last by auto => /> /#.
  by move=> z; wp; call chk_ll; auto => /> /#.
if => //.
seq 6 : true => //.
+ while true (size T - k); last by auto => /> /#.
  by move=> z; auto => /> /#.
sp; if; first by auto => />; smt(dvec_ll).
wp; if; last by auto.
by wp; rnd; auto => />; smt(dvec_ll).
qed.

(* Third rounds of the hint game keep the flag *)
lemma soh_o3_mono : hoare [SOH.o3 : Rp.bH ==> Rp.bH].
proof.
proc; sp; if => //.
sp; if => //.
seq 1 : (Rp.bH); first by auto.
if => //.
seq 4 : (Rp.bH); first by auto.
seq 1 : (Rp.bH).
+ by while (Rp.bH); [wp; call chk_mono; auto | auto].
if => //.
seq 6 : (Rp.bH); first by while (Rp.bH); auto.
by sp; if; [auto => /> /# | if; auto => /> /#].
qed.

(* Adversary commitment queries terminate *)
lemma h0_ll : islossless CntH(HOP).h0.
proof. by proc; inline *; sp; if; [auto | sp; if; [sp; if; auto => />; smt(dcmt_ll) | auto]]. qed.

(* Adversary commitment queries keep the flag *)
lemma h0_mono : hoare [CntH(HOP).h0 : Rp.bH ==> Rp.bH].
proof. by proc; inline *; sp; if; [auto | sp; if; [sp; if; auto | auto]]. qed.

(* Termination with the flag, for the oracle wrappers *)
lemma sop_o2_bh : phoare [SOP.o2 : Rp.bH ==> Rp.bH] = 1%r.
proof. by conseq sop_o2_ll sop_o2_mono. qed.

lemma sop_o3_bh : phoare [SOP.o3 : Rp.bH ==> Rp.bH] = 1%r.
proof. by conseq sop_o3_ll sop_o3_mono. qed.

lemma soh_o3_bh : phoare [SOH.o3 : Rp.bH ==> Rp.bH] = 1%r.
proof. by conseq soh_o3_ll soh_o3_mono. qed.

lemma cop2_bh : phoare [CntO(SOP).o2 : Rp.bH ==> Rp.bH] = 1%r.
proof. by proc; call sop_o2_bh; auto. qed.

lemma coh2_bh : phoare [CntO(SOH).o2 : Rp.bH ==> Rp.bH] = 1%r.
proof. by proc; call sop_o2_bh; auto. qed.

lemma cop3_bh : phoare [CntO(SOP).o3 : Rp.bH ==> Rp.bH] = 1%r.
proof. by proc; call sop_o3_bh; auto. qed.

lemma coh3_bh : phoare [CntO(SOH).o3 : Rp.bH ==> Rp.bH] = 1%r.
proof. by proc; call soh_o3_bh; auto. qed.

lemma h0_bh : phoare [CntH(HOP).h0 : Rp.bH ==> Rp.bH] = 1%r.
proof. by conseq h0_ll h0_mono. qed.

(* The ghost relation survives the oracles that do not respond *)
lemma o1_rh : hoare [CntO(SOH).o1 : relh Fz.fz Rg.fz Rp.cz Rh.dz S.s S.p
                                   ==> relh Fz.fz Rg.fz Rp.cz Rh.dz S.s S.p].
proof. by proc; inline *; sp; if; [sp; if; sp; if; auto | auto]. qed.

lemma subm_rh : hoare [SOR(HCO.CQ, HCO.Rep).subm : relh Fz.fz Rg.fz Rp.cz Rh.dz S.s S.p
                                                  ==> relh Fz.fz Rg.fz Rp.cz Rh.dz S.s S.p].
proof.
proc; sp; while (relh Fz.fz Rg.fz Rp.cz Rh.dz S.s S.p); last by auto.
by wp; if; [inline *; auto | auto].
qed.

lemma sop_o2_rh : hoare [SOP.o2 : relh Fz.fz Rg.fz Rp.cz Rh.dz S.s S.p
                                ==> relh Fz.fz Rg.fz Rp.cz Rh.dz S.s S.p].
proof.
proc; sp; if => //.
sp; if => //.
sp; if.
+ seq 1 : (relh Fz.fz Rg.fz Rp.cz Rh.dz S.s S.p); first by call subm_rh.
  by sp; if; auto.
by inline *; sp; if; auto.
qed.

lemma o2_rh : hoare [CntO(SOH).o2 : relh Fz.fz Rg.fz Rp.cz Rh.dz S.s S.p
                                   ==> relh Fz.fz Rg.fz Rp.cz Rh.dz S.s S.p].
proof. by proc; call sop_o2_rh; auto. qed.

lemma h0_rh : hoare [CntH(HOP).h0 : relh Fz.fz Rg.fz Rp.cz Rh.dz S.s S.p
                                   ==> relh Fz.fz Rg.fz Rp.cz Rh.dz S.s S.p].
proof. by proc; inline *; sp; if; [auto | sp; if; [sp; if; auto | auto]]. qed.

(* The ghost relation holds before any response *)
lemma relh_empty (s : vec) (pp : int -> vec) : relh empty empty empty empty s pp.
proof. by rewrite /relh; smt(mem_empty). qed.

(* A new response keeps the ghost relation *)
lemma relh_set (fz gz : (request * int, vec * vec) fmap) (cz : (request * int, rq) fmap)
               (dz : (request * int, vec) fmap) (s : vec) (pp : int -> vec)
               (k : request * int) (z f g d : vec) (c : rq) :
  relh fz gz cz dz s pp =>
  f = (Rq.( * ) c (lam_of k.`1.`2 k.`2)) ** shr s pp k.`2 + g + d =>
  relh fz.[k <- (z, g)] gz.[k <- (z, f)] cz.[k <- c] dz.[k <- d] s pp.
proof.
rewrite /relh => -[h1 h2] hf; split.
+ by move=> k'; rewrite !mem_set h1.
move=> k'; rewrite !mem_set !get_setE.
case: (k' = k) => [-> /= | hne /=]; first by rewrite hf.
by move=> /h2.
qed.

(* The last honest response of the game with shares equals the one computed from the hint *)
lemma closing_eq (fz gz : (request * int, vec * vec) fmap) (cz : (request * int, rq) fmap)
                 (dz : (request * int, vec) fmap) (lop : (request, int) fmap)
                 (sV : (request, vec * row) fmap) (cV : (request, rq) fmap)
                 (toks : (int, token) fmap) (C : corrset) (V : request) (T : committee) (i : int)
                 (s : vec) (pp : int -> vec) (c : rq) (f g dzk : vec) :
  relh fz gz cz dz s pp =>
  okclose lop sV cV toks gz cz dz C V T i dzk =>
  c = oget cV.[V] =>
  T = V.`2 =>
  f = (Rq.( * ) c (lam_of T i)) ** shr s pp i + g + dzk =>
  f + vmap (fun a => (oget gz.[(V, a)]).`2 - (oget gz.[(V, a)]).`1)
           (filter (fun a => a <> i) (honest T C))
  = ((oget cV.[V]) ** s + (oget sV.[V]).`1
     - vmap (fun j => (Rq.( * ) (oget cV.[V]) (lam_of T j)) ** shr s pp j) (corrupted T C))
    + g + vmap (fun a => (oget fz.[(V, a)]).`2 - (oget fz.[(V, a)]).`1)
               (filter (fun a => a <> i) (honest T C)).
proof.
rewrite /relh; move=> [h1 h2] hok hc hT hf.
move: hok; rewrite /okclose /=.
move=> [#] hl hs hcv hwf hu hi hp hall hd.
have -> : vmap (fun a => (oget fz.[(V, a)]).`2 - (oget fz.[(V, a)]).`1)
               (filter (fun a => a <> i) (honest T C))
        = vmap (fun a => (oget fz.[(V, a)]).`2 - (oget gz.[(V, a)]).`1)
               (filter (fun a => a <> i) (honest T C)).
+ apply vmap_eq => a ha /=.
  have [#] hin _ _ _ _ := hall a ha.
  have hin' : (V, a) \in fz by rewrite h1.
  by have [#] _ _ -> _ := h2 (V, a) hin'.
apply (close_hint T C i (oget toks.[oget lop.[V]]).`tk_i (oget cV.[V]) s pp
                  (oget sV.[V]).`1 (fun a => (oget gz.[(V, a)]).`2)
                  (fun a => (oget fz.[(V, a)]).`2) (fun a => (oget gz.[(V, a)]).`1) f g
                  hwf hu hi hp _ _).
+ move=> a ha hai /=.
  have ha' : a \in filter (fun a => a <> i) (honest T C) by rewrite mem_filter.
  have [#] hin _ _ hcz hdz := hall a ha'.
  have hin' : (V, a) \in fz by rewrite h1.
  have [#] _ _ _ -> := h2 (V, a) hin'.
  by rewrite hcz hdz hT.
by rewrite hf -hc hd.
qed.

(* The closing conditions read the stored responses only through their domain *)
lemma okclose_dom lop sV cV toks (fz1 fz2 : (request * int, vec * vec) fmap) cz dz C V T i dzk :
  (forall k, k \in fz1 <=> k \in fz2) =>
  okclose lop sV cV toks fz1 cz dz C V T i dzk = okclose lop sV cV toks fz2 cz dz C V T i dzk.
proof. by move=> h; rewrite /okclose /=; smt(). qed.

(* The ghost relation fixes the domain *)
lemma relh_dom fz gz cz dz s pp :
  relh fz gz cz dz s pp => (forall k, k \in gz <=> k \in fz).
proof. by rewrite /relh => -[h _] k; rewrite h. qed.

(* The nonce part splits off a response *)
lemma fsplit (a r m : vec) (b : bool) :
  a + r + m = a + ((if b then RqVec.Vector.zerov else r) + m) + (if b then r else RqVec.Vector.zerov).
proof.
case: b => _ /=.
+ smt(RqVec.Vector.ZModule.addrA RqVec.Vector.ZModule.addrC RqVec.Vector.ZModule.add0r).
smt(RqVec.Vector.ZModule.addrA RqVec.Vector.ZModule.addr0).
qed.

(* Checks keep the ghost relation and the cleared flag *)
lemma chk_rel : hoare [SOE(H0C.ER).chk : !Rp.bH /\ relh Fz.fz Rg.fz Rp.cz Rh.dz S.s S.p ==> !Rp.bH /\ relh Fz.fz Rg.fz Rp.cz Rh.dz S.s S.p].
proof.
proc; if.
+ by if; inline *; auto.
by inline *; sp; if; [sp; if; auto | auto].
qed.

(* Third rounds agree until the simulation flag is raised *)
equiv o3_h :
  SOP.o3 ~ SOH.o3 :
  !Rp.bH{2} /\ ={u, T, cs, ws} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd,
      Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.fhp, Rp.prog, Rp.cV, Rp.sV, Rp.cz, Rp.bH, Rh.dz}
  /\ Fz.fz{1} = Rg.fz{2} /\ relh Fz.fz{2} Rg.fz{2} Rp.cz{2} Rh.dz{2} S.s{2} S.p{2}
  ==> if Rp.bH{2} then Rp.bH{1} else ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd,
      Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.fhp, Rp.prog, Rp.cV, Rp.sV, Rp.cz, Rp.bH, Rh.dz}
  /\ Fz.fz{1} = Rg.fz{2} /\ relh Fz.fz{2} Rg.fz{2} Rp.cz{2} Rh.dz{2} S.s{2} S.p{2}.
proof.
proc.
seq 1 1 : (!Rp.bH{2} /\ ={u, T, cs, ws, out} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd,
      Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.fhp, Rp.prog, Rp.cV, Rp.sV, Rp.cz, Rp.bH, Rh.dz}
  /\ Fz.fz{1} = Rg.fz{2} /\ relh Fz.fz{2} Rg.fz{2} Rp.cz{2} Rh.dz{2} S.s{2} S.p{2}); first by auto.
if => //.
seq 1 1 : (!Rp.bH{2} /\ ={u, T, cs, ws, out, tok} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd,
      Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.fhp, Rp.prog, Rp.cV, Rp.sV, Rp.cz, Rp.bH, Rh.dz}
  /\ Fz.fz{1} = Rg.fz{2} /\ relh Fz.fz{2} Rg.fz{2} Rp.cz{2} Rh.dz{2} S.s{2} S.p{2}); first by auto.
if => //.
seq 1 1 : (!Rp.bH{2} /\ ={u, T, cs, ws, out, tok, d} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd,
      Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.fhp, Rp.prog, Rp.cV, Rp.sV, Rp.cz, Rp.bH, Rh.dz}
  /\ Fz.fz{1} = Rg.fz{2} /\ relh Fz.fz{2} Rg.fz{2} Rp.cz{2} Rh.dz{2} S.s{2} S.p{2}); first by auto.
if => //.
seq 5 5 : (!Rp.bH{2} /\ ={u, T, cs, ws, out, tok, d, okk, Ex.cur} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd,
      Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.fhp, Rp.prog, Rp.cV, Rp.sV, Rp.cz, Rp.bH, Rh.dz}
  /\ Fz.fz{1} = Rg.fz{2} /\ relh Fz.fz{2} Rg.fz{2} Rp.cz{2} Rh.dz{2} S.s{2} S.p{2}).
+ conseq (_ : ={u, T, cs, ws, out, tok, d} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd,
      Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.fhp, Rp.prog, Rp.cV, Rp.sV, Rp.cz, Rp.bH, Rh.dz} /\ Fz.fz{1} = Rg.fz{2}
             ==> ={u, T, cs, ws, out, tok, d, okk, Ex.cur} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd,
      Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.fhp, Rp.prog, Rp.cV, Rp.sV, Rp.cz, Rp.bH, Rh.dz} /\ Fz.fz{1} = Rg.fz{2})
         _ (_ : !Rp.bH /\ relh Fz.fz Rg.fz Rp.cz Rh.dz S.s S.p ==> !Rp.bH /\ relh Fz.fz Rg.fz Rp.cz Rh.dz S.s S.p) => //.
  + by wp; while (!Rp.bH /\ relh Fz.fz Rg.fz Rp.cz Rh.dz S.s S.p); [wp; call chk_rel; auto | auto].
  by sim (: Fz.fz{1} = Rg.fz{2}).
if => //.
seq 6 6 : (!Rp.bH{2} /\ ={u, T, cs, ws, out, tok, d, okk, Ex.cur, c, ys, mkc} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd,
      Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.fhp, Rp.prog, Rp.cV, Rp.sV, Rp.cz, Rp.bH, Rh.dz}
  /\ Fz.fz{1} = Rg.fz{2} /\ relh Fz.fz{2} Rg.fz{2} Rp.cz{2} Rh.dz{2} S.s{2} S.p{2}).
+ conseq (_ : ={u, T, cs, ws, out, tok, d, okk, Ex.cur} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd,
      Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.fhp, Rp.prog, Rp.cV, Rp.sV, Rp.cz, Rp.bH, Rh.dz} /\ Fz.fz{1} = Rg.fz{2}
             ==> ={u, T, cs, ws, out, tok, d, okk, Ex.cur, c, ys, mkc} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd,
      Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.fhp, Rp.prog, Rp.cV, Rp.sV, Rp.cz, Rp.bH, Rh.dz}
                 /\ Fz.fz{1} = Rg.fz{2})
         _ (_ : !Rp.bH /\ relh Fz.fz Rg.fz Rp.cz Rh.dz S.s S.p ==> !Rp.bH /\ relh Fz.fz Rg.fz Rp.cz Rh.dz S.s S.p) => //.
  + by wp; while (!Rp.bH /\ relh Fz.fz Rg.fz Rp.cz Rh.dz S.s S.p); auto.
  by sim (: Fz.fz{1} = Rg.fz{2}).
sp 3 4.
if => //.
+ by wp; rnd{2}; auto => />; smt(dvec_ll).
if => //.
+ wp; rnd; auto => />.
  move=> &h bH hb hrel hdup hys zL _ hnot.
  have hT : T{h} = (oget S.req{h}.[u{h}]).`2 by smt().
  apply relh_set => //.
  by rewrite /= -hT; apply fsplit.
if{2}; last first.
+ by auto => />; smt().
auto => />.
move=> &h bH hb hrel hdup hnot hcv.
have hc : c{h} = oget Rp.cV{h}.[oget S.req{h}.[u{h}]] by smt().
have hT : T{h} = (oget S.req{h}.[u{h}]).`2 by smt().
have hok : okclose Rx.lop{h} Rp.sV{h} Rp.cV{h} S.toks{h} Rg.fz{h} Rp.cz{h} Rh.dz{h} S.cs{h}
             (oget S.req{h}.[u{h}]) T{h} tok{h}.`tk_i
             (if Rx.lop{h}.[oget S.req{h}.[u{h}]] = Some u{h} then tok{h}.`tk_r
              else RqVec.Vector.zerov) by smt().
have heq := closing_eq Fz.fz{h} Rg.fz{h} Rp.cz{h} Rh.dz{h} Rx.lop{h} Rp.sV{h} Rp.cV{h} S.toks{h}
              S.cs{h} (oget S.req{h}.[u{h}]) T{h} tok{h}.`tk_i S.s{h} S.p{h} c{h}
              ((Rq.( * ) c{h} (lam_of T{h} tok{h}.`tk_i)) ** shr S.s{h} S.p{h} tok{h}.`tk_i
               + tok{h}.`tk_r + mkc{h})
              ((if Rx.lop{h}.[oget S.req{h}.[u{h}]] = Some u{h} then RqVec.Vector.zerov
                else tok{h}.`tk_r) + mkc{h})
              (if Rx.lop{h}.[oget S.req{h}.[u{h}]] = Some u{h} then tok{h}.`tk_r
               else RqVec.Vector.zerov)
              hrel hok hc hT (fsplit _ _ _ _).
rewrite heq /=.
apply relh_set => //.
by rewrite /= -hT; apply fsplit.
qed.

section HintHop.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -Fz, -Bd, -Ex, -Rx, -Rp, -Rh, -Rg, -H0H.QRO,
                         -H0C.QRO, -H1O.QRO, -HCO.QRO, -H0H.LC, -H0H.CQ, -H0C.CQ, -H0C.Sim,
                         -H0C.ER, -HCO.CQ, -HCO.Rep}.

declare axiom A_ll (H <: HOr {-A}) (O <: SOr {-A}) :
  islossless H.h0 => islossless H.h1 => islossless H.hc =>
  islossless O.o1 => islossless O.o2 => islossless O.o3 =>
  islossless A(H, O).forge.

(* The game with shares and the hint game agree until the simulation flag is raised *)
lemma gp_gh &m : Pr[GP(A).main() @ &m : res /\ !Rp.bH] <= Pr[GH(A).main() @ &m : res].
proof.
byequiv (_ : ={glob A} ==> (!Rp.bH{2} => ={res, Rp.bH}) /\ (Rp.bH{2} => Rp.bH{1})) => //;
  last by smt().
proc.
wp.
call (_ : Rp.bH, ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd,
      Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.fhp, Rp.prog, Rp.cV, Rp.sV, Rp.cz, Rp.bH, Rh.dz}
  /\ Fz.fz{1} = Rg.fz{2} /\ relh Fz.fz{2} Rg.fz{2} Rp.cz{2} Rh.dz{2} S.s{2} S.p{2}, Rp.bH{1}).
+ by move=> H O ho1 ho2 ho3 hh0 hh1 hhc; apply (A_ll H O).
+ conseq (_ : ={i, mu} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd,
      Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.fhp, Rp.prog, Rp.cV, Rp.sV, Rp.cz, Rp.bH, Rh.dz} /\ Fz.fz{1} = Rg.fz{2}
             ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd,
      Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.fhp, Rp.prog, Rp.cV, Rp.sV, Rp.cz, Rp.bH, Rh.dz} /\ Fz.fz{1} = Rg.fz{2}) _ o1_rh => />.
  by proc; inline *; sim (: Fz.fz{1} = Rg.fz{2}).
+ by move=> &2 _; exact o1_bh.
+ by move=> &1; conseq o1_bhh.
+ conseq (_ : ={u, T, cs} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd,
      Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.fhp, Rp.prog, Rp.cV, Rp.sV, Rp.cz, Rp.bH, Rh.dz} /\ Fz.fz{1} = Rg.fz{2}
             ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd,
      Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.fhp, Rp.prog, Rp.cV, Rp.sV, Rp.cz, Rp.bH, Rh.dz} /\ Fz.fz{1} = Rg.fz{2}) _ o2_rh => />.
  by proc; inline CntO(SOP).o2 CntO(SOH).o2; sim (: Fz.fz{1} = Rg.fz{2}).
+ by move=> &2 _; exact cop2_bh.
+ by move=> &1; conseq coh2_bh.
+ by proc; wp; call o3_h; auto.
+ by move=> &2 _; exact cop3_bh.
+ by move=> &1; conseq coh3_bh.
+ conseq (_ : ={x} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd,
      Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.fhp, Rp.prog, Rp.cV, Rp.sV, Rp.cz, Rp.bH, Rh.dz} /\ Fz.fz{1} = Rg.fz{2}
             ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Bd,
      Ex.ix, Ex.n, Ex.dn, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H0C.CQ,
      glob H0C.Sim, glob H0C.ER, glob H1O.QRO, HCO.QRO.fh, Rx.nr, Rx.pts, Rx.bP, Rx.bC, Rx.lop,
      Rp.fhp, Rp.prog, Rp.cV, Rp.sV, Rp.cz, Rp.bH, Rh.dz} /\ Fz.fz{1} = Rg.fz{2}) _ h0_rh => />.
  by proc; inline *; sim (: Fz.fz{1} = Rg.fz{2}).
+ by move=> &2 _; exact h0_bh.
+ by move=> &1; conseq h0_bh.
+ by proc; inline *; auto.
+ by move=> &2 _; proc; inline *; auto.
+ by move=> &1; proc; inline *; auto.
+ by proc; inline *; auto.
+ by move=> &2 _; proc; inline *; auto.
+ by move=> &1; proc; inline *; auto.
inline *; auto.
call (_ : true).
by auto => />; smt(relh_empty).
qed.

end section HintHop.
