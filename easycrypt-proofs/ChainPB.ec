require import AllCore Int List Distr DList FMap FSet Real RealExp Finite StdOrder StdBigop FelTactic.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption.
require import Protocol Notions Privacy Extract FinEnum ChainBase ChainGame ChainCol ChainSim.
require import ChainDead ChainLazy ChainFlag ChainExt ChainRep ChainProg.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.
import Bigreal.BRA.

(* ---------- the flags of the programming in the game GP ----------

   The flag Rx.bC (a completion beyond the budget of qsig programmings) is never raised under the
   query bound, and the flag Rx.bP (a point programmed twice) is raised with probability at most
   qsig^2 pw2 by the regularity of the aggregate commitment. *)

(* Submissions leave the programming records alone *)
lemma subm_nr (nr0 : int) (bC0 : bool) (cs0 : int) :
  hoare [SOR(HCO.CQ, HCO.Rep).subm : Rx.nr = nr0 /\ Rx.bC = bC0 /\ Cnt.cs = cs0 ==>
                                     Rx.nr = nr0 /\ Rx.bC = bC0 /\ Cnt.cs = cs0].
proof. by proc; while (Rx.nr = nr0 /\ Rx.bC = bC0 /\ Cnt.cs = cs0); [inline *; auto | auto]. qed.

(* The completions beyond the budget are counted by the signing queries *)
op [opaque] nrinv (nr cs : int) (bC : bool) : bool = 0 <= nr /\ nr + b2i bC <= cs /\ (bC => qsig <= nr).

lemma o1_nr : hoare [CntO(SOP).o1 : nrinv Rx.nr Cnt.cs Rx.bC ==> nrinv Rx.nr Cnt.cs Rx.bC].
proof.
proc; inline SOP.o1; sp; if; last by auto; rewrite /nrinv => &h />; smt().
by inline *; sp; if; sp; if; auto; rewrite /nrinv => &h />; smt().
qed.

lemma o2_nr : hoare [CntO(SOP).o2 : nrinv Rx.nr Cnt.cs Rx.bC ==> nrinv Rx.nr Cnt.cs Rx.bC].
proof.
proc; inline SOP.o2; sp; if; last by auto; rewrite /nrinv => &h />; smt().
sp; if; last by auto; rewrite /nrinv => &h />; smt().
sp; if.
+ exlim Rx.nr, Rx.bC, Cnt.cs => nr0 bC0 cs0.
  seq 1 : (Rx.nr = nr0 /\ Rx.bC = bC0 /\ Cnt.cs = cs0 /\ nrinv (nr0 + 0) (cs0 - 1) bC0).
  + call (subm_nr nr0 bC0 cs0); auto; rewrite /nrinv => &h />; smt().
  sp; if; auto; rewrite /nrinv => &h />; smt().
by inline *; sp; if; auto; rewrite /nrinv => &h />; smt().
qed.

lemma o3_nr : hoare [CntO(SOP).o3 : nrinv Rx.nr Cnt.cs Rx.bC ==> nrinv Rx.nr Cnt.cs Rx.bC].
proof.
proc; inline SOP.o3; sp; if; last by auto; rewrite /nrinv => &h />; smt().
sp; if; last by auto; rewrite /nrinv => &h />; smt().
sp; if; last by auto; rewrite /nrinv => &h />; smt().
seq 4 : (nrinv Rx.nr (Cnt.cs - 1) Rx.bC); first by auto; rewrite /nrinv => &h />; smt().
seq 1 : (nrinv Rx.nr (Cnt.cs - 1) Rx.bC).
+ while (nrinv Rx.nr (Cnt.cs - 1) Rx.bC); last by auto.
  wp; call (_ : true); last by auto.
  by sp; if; [if; inline *; auto | inline *; sp; if; [sp; if; auto | auto]].
if; last by auto; rewrite /nrinv => &h />; smt().
seq 6 : (nrinv Rx.nr (Cnt.cs - 1) Rx.bC).
+ by while (nrinv Rx.nr (Cnt.cs - 1) Rx.bC); auto.
sp; if; [auto; rewrite /nrinv => &h />; smt() | if; auto; rewrite /nrinv => &h />; smt()].
qed.

lemma h0_nr : hoare [CntH(HOP).h0 : nrinv Rx.nr Cnt.cs Rx.bC ==> nrinv Rx.nr Cnt.cs Rx.bC].
proof. by proc; inline *; sp; if; [auto | sp; if; [sp; if; auto | auto]]. qed.

lemma h1_nr : hoare [CntH(HOP).h1 : nrinv Rx.nr Cnt.cs Rx.bC ==> nrinv Rx.nr Cnt.cs Rx.bC].
proof. by proc; inline *; auto. qed.

lemma hc_nr : hoare [CntH(HOP).hc : nrinv Rx.nr Cnt.cs Rx.bC ==> nrinv Rx.nr Cnt.cs Rx.bC].
proof. by proc; inline *; auto. qed.

section Budget.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -Fz, -Bd, -Ex, -Rx, -Rp, -Rh, -H0H.QRO, -H0C.QRO,
                         -H1O.QRO, -HCO.QRO, -H0H.LC, -H0H.CQ, -H0C.CQ, -H0C.Sim, -H0C.ER,
                         -HCO.CQ, -HCO.Rep}.

declare axiom A_bnd (H <: HOr {-A, -Cnt}) (O <: SOr {-A, -Cnt}) :
  hoare [A(CntH(H), CntO(O)).forge : Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 ==>
         Cnt.c0 <= qh0 /\ Cnt.c1 <= qh1 /\ Cnt.cc <= qhc /\ Cnt.cs <= qsig].

local lemma forge_nr :
  hoare [A(CntH(HOP), CntO(SOP)).forge :
    Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 /\ Rx.nr = 0 /\ !Rx.bC ==>
    Cnt.cs <= qsig /\ nrinv Rx.nr Cnt.cs Rx.bC].
proof.
conseq (A_bnd HOP SOP) (_ : nrinv Rx.nr Cnt.cs Rx.bC ==> nrinv Rx.nr Cnt.cs Rx.bC) => //.
+ by move=> &h /> *; rewrite /nrinv /b2i.
proc (nrinv Rx.nr Cnt.cs Rx.bC) => //.
+ exact o1_nr.
+ exact o2_nr.
+ exact o3_nr.
+ exact h0_nr.
+ exact h1_nr.
+ exact hc_nr.
qed.

(* No completion goes beyond the budget *)
lemma gp_bc : hoare [GP(A).main : true ==> !Rx.bC /\ Cnt.cs <= qsig].
proof.
proc; wp.
call forge_nr.
auto; call (_ : true); inline *; auto => /> *.
rewrite /nrinv => *; smt().
qed.

lemma gp_bc_pr &m : Pr[GP(A).main() @ &m : Rx.bC] = 0%r.
proof. by byphoare => //; hoare; conseq gp_bc => /#. qed.

end section Budget.

(* ---------- a point programmed twice ---------- *)

section Twice.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -Fz, -Bd, -Ex, -Rx, -Rp, -Rh, -H0H.QRO, -H0C.QRO,
                         -H1O.QRO, -HCO.QRO, -H0H.LC, -H0H.CQ, -H0C.CQ, -H0C.Sim, -H0C.ER,
                         -HCO.CQ, -HCO.Rep}.

declare axiom A_bnd (H <: HOr {-A, -Cnt}) (O <: SOr {-A, -Cnt}) :
  hoare [A(CntH(H), CntO(O)).forge : Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 ==>
         Cnt.c0 <= qh0 /\ Cnt.c1 <= qh1 /\ Cnt.cc <= qhc /\ Cnt.cs <= qsig].

declare axiom reg_agg (Y x : row) :
  mu dnp (fun (s : vec * row) => liftw (rndw (liftc (popn s) + Y)) = x) <= pw2.

local lemma pw2_ge0 : 0%r <= pw2.
proof. by have := reg_agg witness witness; smt(mu_bounded). qed.

(* A fresh nonce fixes a given point with small probability *)
local lemma pt_eq (t : row) (m0 : msg) (ws : row list) (p : int) (y : hcin) :
  0 <= p < size ws => mu dnp (fun s => xpt t m0 (put ws p (popn s)) = y) <= pw2.
proof.
move=> hp.
apply (StdOrder.RealOrder.ler_trans
         (mu dnp (fun s => liftw (rndw (liftc (popn s)
                    + (rowmap liftc ws - liftc (nth witness ws p)))) = y.`1))).
+ by apply mu_sub => s /= <-; rewrite /xpt /aggw rowmap_put.
exact reg_agg.
qed.

(* ... and one of given points with probability at most their number times pw2 *)
local lemma pt_mem (t : row) (m0 : msg) (ws : row list) (p : int) (pts : hcin list) :
  0 <= p < size ws =>
  mu dnp (fun s => xpt t m0 (put ws p (popn s)) \in pts) <= (size pts)%r * pw2.
proof.
move=> hp; elim: pts => [| y pts ih].
+ by rewrite (mu_eq _ _ pred0) // mu0.
rewrite (mu_eq _ _ (predU (fun s => xpt t m0 (put ws p (popn s)) = y)
                          (fun s => xpt t m0 (put ws p (popn s)) \in pts))).
+ by move=> s; rewrite /predU in_cons.
rewrite mu_or /=.
have := pt_eq t m0 ws p y hp.
have := mu_bounded dnp (predI (fun s => xpt t m0 (put ws p (popn s)) = y)
                              (fun s => xpt t m0 (put ws p (popn s)) \in pts)).
smt().
qed.

(* Submissions leave the programmed points alone *)
local lemma subm_bp (p0 : hcin list) (nr0 : int) (b0 : bool) :
  hoare [SOR(HCO.CQ, HCO.Rep).subm : Rx.pts = p0 /\ Rx.nr = nr0 /\ Rx.bP = b0 ==>
                                     Rx.pts = p0 /\ Rx.nr = nr0 /\ Rx.bP = b0].
proof. by proc; while (Rx.pts = p0 /\ Rx.nr = nr0 /\ Rx.bP = b0); [inline *; auto | auto]. qed.

lemma gp_bp_fel &m :
  Pr[GP(A).main() @ &m : Rx.bP /\ Cnt.cs <= qsig] <= bigi predT (fun _ => qsig%r * pw2) 0 qsig.
proof.
fel 51 Cnt.cs (fun _ => qsig%r * pw2) qsig Rx.bP
    [CntO(SOP).o1 : true; CntO(SOP).o2 : true; CntO(SOP).o3 : true;
     CntH(HOP).h0 : false; CntH(HOP).h1 : false; CntH(HOP).hc : false]
    (size Rx.pts = Rx.nr /\ 0 <= Rx.nr <= qsig).
+ done.
+ smt().
+ by inline *; auto; call (_ : true); auto => />; smt(ge0_qsig).
+ hoare; [smt(pw2_ge0) | proc; inline SOP.o1; sp; if; [inline *; sp; if; sp; if; auto | auto]].
+ move=> c; proc; inline SOP.o1; sp; if; last by auto => /> /#.
  by inline *; sp; if; sp; if; auto => /> /#.
+ by move=> b c; conseq (_ : false ==> _) => //.
+ proc; inline SOP.o2; sp; if; last by hoare; [smt(pw2_ge0) | auto].
  sp; if; last by hoare; [smt(pw2_ge0) | auto].
  sp; if; last by hoare; [smt(pw2_ge0) | inline *; sp; if; auto].
  seq 2 : true 1%r (qsig%r * pw2) 0%r 0%r
          (size Rx.pts = Rx.nr /\ 0 <= Rx.nr <= qsig /\ !Rx.bP /\ ok2 tok T0 cs0
           /\ vr = (tok.`tk_msg, T0, cs0)).
  + wp; ecall (subm_bp Rx.pts Rx.nr Rx.bP); auto => /> /#.
  + trivial.
  + if.
    - seq 2 : (x \in Rx.pts) (qsig%r * pw2) 1%r 1%r 0%r (!Rx.bP).
      + by auto.
      + wp; rnd (fun (s0 : vec * row) =>
          xpt S.t vr.`1 (put (wsV S.toks S.req S.cs H0C.ER.xs Ex.ix vr) (index tok.`tk_i T0) (popn s0))
          \in Rx.pts).
        skip => &h /> hn0 hn1 hb hph huq hsz hin hiT hcs hown hnr.
        have hp : 0 <= index tok{h}.`tk_i T0{h} < size (wsV S.toks{h} S.req{h} S.cs{h} H0C.ER.xs{h} Ex.ix{h}
                                                        (tok{h}.`tk_msg, T0{h}, cs0{h})).
        * by rewrite /wsV size_map /= index_ge0 index_mem.
        have := pt_mem S.t{h} tok{h}.`tk_msg _ _ Rx.pts{h} hp.
        have : (size Rx.pts{h})%r * pw2 <= qsig%r * pw2 by smt(pw2_ge0).
        smt().
      + trivial.
      + trivial.
      + by hoare; auto => />.
      + smt().
    hoare; [smt(pw2_ge0) | auto].
  + hoare; wp; call (_ : true); [by while true; [inline *; auto | auto] | auto].
  trivial.
+ move=> c; proc; inline SOP.o2; sp; if; last by auto => /> /#.
  sp; if; last by auto => /> /#.
  sp; if; last by inline *; sp; if; auto => /> /#.
  seq 2 : (c < Cnt.cs /\ size Rx.pts = Rx.nr /\ 0 <= Rx.nr <= qsig).
  + by wp; ecall (subm_bp Rx.pts Rx.nr Rx.bP); auto => /> /#.
  by sp; if; auto => /> /#.
+ by move=> b c; conseq (_ : false ==> _) => //.
+ hoare; [smt(pw2_ge0) | ].
  proc; inline SOP.o3; sp; if; last by auto.
  sp; if; last by auto.
  sp; if; last by auto.
  seq 4 : (!Rx.bP); first by auto.
  seq 1 : (!Rx.bP).
  + while (!Rx.bP); last by auto.
    wp; call (_ : true); last by auto.
    by sp; if; [if; inline *; auto | inline *; sp; if; [sp; if; auto | auto]].
  if; last by auto.
  seq 6 : (!Rx.bP); first by while (!Rx.bP); auto.
  by sp; if; [auto | if; auto].
+ move=> c; proc; inline SOP.o3; sp; if; last by auto => /> /#.
  sp; if; last by auto => /> /#.
  sp; if; last by auto => /> /#.
  seq 4 : (c < Cnt.cs /\ size Rx.pts = Rx.nr /\ 0 <= Rx.nr <= qsig); first by auto => /> /#.
  seq 1 : (c < Cnt.cs /\ size Rx.pts = Rx.nr /\ 0 <= Rx.nr <= qsig).
  + while (c < Cnt.cs /\ size Rx.pts = Rx.nr /\ 0 <= Rx.nr <= qsig); last by auto.
    wp; call (_ : true); last by auto.
    by sp; if; [if; inline *; auto | inline *; sp; if; [sp; if; auto | auto]].
  if; last by auto.
  seq 6 : (c < Cnt.cs /\ size Rx.pts = Rx.nr /\ 0 <= Rx.nr <= qsig).
  + by while (c < Cnt.cs /\ size Rx.pts = Rx.nr /\ 0 <= Rx.nr <= qsig); auto.
  by sp; if; [auto | if; auto].
+ by move=> b c; conseq (_ : false ==> _) => //.
qed.

(* A point is programmed twice with probability at most qsig^2 pw2 *)
lemma gp_bp &m : Pr[GP(A).main() @ &m : Rx.bP] <= qsig%r * (qsig%r * pw2).
proof.
have h1 := gp_bp_fel &m.
have h0 : Pr[GP(A).main() @ &m : Rx.bP /\ !(Cnt.cs <= qsig)] = 0%r.
+ byphoare => //; hoare; conseq (gp_bc A A_bnd) => /#.
have hs : bigi predT (fun _ => qsig%r * pw2) 0 qsig = qsig%r * (qsig%r * pw2).
+ by rewrite sumri_const; smt(ge0_qsig).
rewrite Pr[mu_split (Cnt.cs <= qsig)] h0 /=.
smt().
qed.

end section Twice.
