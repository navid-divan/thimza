require import AllCore Int List Distr DList FMap FSet Real RealExp Finite StdOrder StdBigop.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption.
require import Protocol Notions Privacy Extract FinEnum ChainBase ChainGame ChainCol ChainSim.
require import ChainDead ChainLazy ChainFlag ChainExt ChainRep ChainProg ChainHint ShamirHide ChainFin.
require import ChainCons ChainPB ChainGA ChainB2 ChainB3 ChainB1a ChainB1b ChainB1c ChainB1d.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

(* ---------- Theorem main as one statement ----------

   G0(A) is the TS-UF-4 experiment in the opening semantics: Thimza with the four hash
   functions as quantum random oracles, the corruption of A, the key generation, the signing
   oracles O1, O2, O3 with their checks and erasure, and the winning condition win4 on the
   opening log.  The statement below composes every hop of the chain and every flag bound for
   one adversary A: the PRF term (reduction B1), the HintMLWE term (reduction B2), the
   SelfTargetMSIS term (reduction B3) and the statistical loss eps_main, whose terms are, in
   order, the H1 collision of the simulation, the lazy commitments, the extraction, the
   reprogramming of Hc, the flag bP (the flag bC has probability 0, and the hint flag bH is
   covered by bP and bC), and the flags b1, b2, b3. *)

op eps_ext : real =
  8%r * lx%r * (qx + lx)%r * sqrt (2%r * p_max dcmt)
  + (8%r * lx%r * (qx + 1)%r * sqrt (2%r * p_max dcmt)
     + (40%r * exp 1%r ^ 2 * (qx + lx + 1)%r ^ 3 + 2%r) * p_max dcmt).

op eps_b1 : real =
  2%r * (qh0 + tthr * qsig)%r * sqrt (qsig%r * pw) + (qsig * qsig)%r * pw
  + 27%r * (qh0 + (1 + tthr) * qsig + 2)%r ^ 3 * p_max dcmt
  + (qsig * (2 * qsig - 1))%r * pw.

op eps_main : real =
  27%r * (qh1 + 2 * qsig + 2)%r ^ 3 * p_max dview
  + (2%r * (qh0 + tthr * qsig)%r * sqrt (qsig%r * pw) + (qsig * qsig)%r * pw)
  + eps_ext
  + qsig%r * (sqrt (qc%r * pw2) + qc%r * pw2 / 2%r)
  + qsig%r * (qsig%r * pw2)
  + eps_b1
  + qsig%r * (((1 + tthr) * qsig)%r * p_max dcmt)
  + 27%r * (qh1 + qsig + 2)%r ^ 3 * p_max dview.

section Main.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -Fz, -Bd, -Ex, -Rx, -Rp, -Rh, -Rg, -Ry, -Kb, -HM,
                         -Lg1, -Bx, -Lc0, -Lc, -H0H.QRO, -H0C.QRO, -H1O.QRO, -HCO.QRO, -H0H.LC,
                         -H0H.CQ, -H1O.CQ, -H0C.CQ, -H0C.Sim, -H0C.ER, -HCO.CQ, -HCO.Rep}.

(* The adversary terminates when its oracles do *)
declare axiom A_ll (H <: HOr {-A}) (O <: SOr {-A}) :
  islossless H.h0 => islossless H.h1 => islossless H.hc =>
  islossless O.o1 => islossless O.o2 => islossless O.o3 =>
  islossless A(H, O).forge.

(* The adversary makes at most qh0, qh1, qhc hash queries and qsig signing queries *)
declare axiom A_bnd (H <: HOr {-A, -Cnt}) (O <: SOr {-A, -Cnt}) :
  hoare [A(CntH(H), CntO(O)).forge : Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 ==>
         Cnt.c0 <= qh0 /\ Cnt.c1 <= qh1 /\ Cnt.cc <= qhc /\ Cnt.cs <= qsig].

(* The encoding of the inputs of H1 is injective on well formed requests *)
declare axiom e1_inj (t t' : row) (V V' : request) :
  wfreq V => wfreq V' => e1 t V.`1 V.`2 V.`3 = e1 t' V'.`1 V'.`2 V'.`3 => t = t' /\ V = V'.

(* Min-entropy of an opening and of an aggregated rounded first message *)
declare axiom reg_open :
  forall (w : row), mu (dnonce `*` dnoiser) (fun (s : vec * row) => rndc (commit s.`1 s.`2) = w) <= pw.

declare axiom reg_agg (Y x : row) :
  mu dnp (fun (s : vec * row) => liftw (rndw (liftc (popn s) + Y)) = x) <= pw2.

(* The evaluation points and their differences are units *)
declare axiom alpha_unit : forall j, 1 <= j <= nmax => Rq.ComRingDflInv.unit (alpha j).

declare axiom alpha_sep : forall i j, 1 <= i <= nmax => 1 <= j <= nmax => i <> j =>
  Rq.ComRingDflInv.unit (Rq.( + ) (alpha i) (Rq.([-]) (alpha j))).

lemma thimza_main &m :
  rounding_fact =>
  Pr[G0(A).main() @ &m : res]
  <= `|Pr[MPRFG(B1(A)).real() @ &m : res] - Pr[MPRFG(B1(A)).ideal() @ &m : res]|
     + `|Pr[HMLWE(B2(A)).main(true) @ &m : res] - Pr[HMLWE(B2(A)).main(false) @ &m : res]|
     + Pr[STM(B3(A)).main() @ &m : res]
     + eps_main.
proof.
move=> hr.
have h1 := hop_prf A &m.
have h2 := g1_g1s A A_ll A_bnd e1_inj &m.
have h3 := g1s_g1t A &m.
have h4 := g1t_lazy A reg_open A_bnd &m.
have h5 := gl_ga A &m.
have h6 := ga_split A &m.
have h7 := ga_ext A A_bnd &m.
have h8 := ge_rep A A_bnd reg_agg &m.
have h9 := rep_gp A reg_agg &m.
have h10 := gp_split A alpha_sep &m.
have h11 := gp_gh A A_ll &m.
have h12 := gh_bound A A_ll alpha_unit &m hr.
have h13 := gp_bc_pr A A_bnd &m.
have h14 := gp_bp A A_bnd reg_agg &m.
have h15 := ga_b2 A A_bnd &m.
have h16 := ga_b3 A e1_inj A_bnd &m.
have h17 := ga_b1 A A_bnd reg_open &m.
have h18 : Pr[GP(A).main() @ &m : Rx.bP \/ Rx.bC]
           <= Pr[GP(A).main() @ &m : Rx.bP] + Pr[GP(A).main() @ &m : Rx.bC].
+ rewrite Pr[mu_or].
  have : 0%r <= Pr[GP(A).main() @ &m : Rx.bP /\ Rx.bC] by rewrite Pr[mu_ge0].
  smt().
rewrite /eps_main /eps_ext /eps_b1.
smt().
qed.

end section Main.
