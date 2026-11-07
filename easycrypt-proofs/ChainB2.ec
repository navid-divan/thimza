require import AllCore Int List Distr DList FMap FSet Real RealExp Finite StdOrder StdBigop FelTactic.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption.
require import Protocol Notions Privacy Extract FinEnum ChainBase ChainGame ChainCol ChainSim.
require import ChainDead ChainLazy ChainFlag ChainGA.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.
import Bigreal.BRA.

(* ---------- the second flag: a fresh first message equal to an existing one ---------- *)

(* The tokens and responded requests count the existing first messages *)
op [opaque] b2inv (toks : (int, token) fmap) (req : (int, request) fmap) (lr : alog) (cs : int) : bool =
  card (fdom toks) <= cs /\ size lr <= cs
  /\ (forall (V : request) a, (V, a) \in lr => size V.`3 = tthr)
  /\ (forall u, u \in toks => (oget toks.[u]).`tk_phase <> 1 =>
        u \in req /\ size (oget req.[u]).`3 = tthr).

(* The existing first messages *)
op cmts (toks : (int, token) fmap) (lr : alog) : cmt list =
  map (fun u => (oget toks.[u]).`tk_cmt) (elems (fdom toks)) ++ flatten (map (fun (Va : request * int) => Va.`1.`3) lr).

lemma cmts_mem (toks : (int, token) fmap) (lr : alog) (c : cmt) :
  dupc toks c \/ seenc lr c => c \in cmts toks lr.
proof.
rewrite /cmts mem_cat => -[[u [hu hc]] | [V a [hV hc]]].
+ left; rewrite -hc; apply (map_f (fun u => (oget toks.[u]).`tk_cmt)).
  by rewrite -memE mem_fdom.
by right; apply/flatten_mapP; exists (V, a).
qed.

lemma cmts_size (toks : (int, token) fmap) (lr : alog) (cs : int) :
  card (fdom toks) <= cs => size lr <= cs => (forall (V : request) a, (V, a) \in lr => size V.`3 = tthr) =>
  size (cmts toks lr) <= (1 + tthr) * cs.
proof.
move=> hc hl hv; rewrite /cmts size_cat size_map -cardE.
have := flatten_size (fun (Va : request * int) => Va.`1.`3) lr tthr _.
+ by move=> [V a] /= h; rewrite (hv V a h).
smt(thr_range).
qed.

(* A fresh first message hits an existing one with small probability *)
lemma fresh_cmt (toks : (int, token) fmap) (lr : alog) (cs : int) :
  card (fdom toks) <= cs => size lr <= cs => (forall (V : request) a, (V, a) \in lr => size V.`3 = tthr) =>
  mu dcmt (fun c => dupc toks c \/ seenc lr c) <= ((1 + tthr) * cs)%r * p_max dcmt.
proof.
move=> hc hl hv.
apply (StdOrder.RealOrder.ler_trans (mu dcmt (mem (cmts toks lr)))).
+ by apply mu_sub => c /=; apply cmts_mem.
apply (StdOrder.RealOrder.ler_trans ((size (cmts toks lr))%r * p_max dcmt)).
+ by apply mu_mem_le_mu1 => x; apply pmax_upper_bound.
apply StdOrder.RealOrder.ler_wpmul2r; first exact pmax_ge0.
by rewrite le_fromint; apply (cmts_size toks lr cs hc hl hv).
qed.

section B2.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -Fz, -Bd, -H0H.QRO, -H0C.QRO, -H1O.QRO,
                         -HCO.QRO, -H0H.LC, -H0H.CQ}.

declare axiom A_bnd (H <: HOr {-A, -Cnt}) (O <: SOr {-A, -Cnt}) :
  hoare [A(CntH(H), CntO(O)).forge : Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 ==>
         Cnt.c0 <= qh0 /\ Cnt.c1 <= qh1 /\ Cnt.cc <= qhc /\ Cnt.cs <= qsig].

lemma gag_bnd : hoare [GAg(A).main : true ==> Cnt.cs <= qsig].
proof.
proc; wp; call (A_bnd (HOL(H0H.LC)) SOA2).
by inline *; auto; call (_ : true); auto.
qed.

lemma gag_b2_fel &m :
  Pr[GAg(A).main() @ &m : Bd.b2 /\ Cnt.cs <= qsig]
  <= bigi predT (fun _ => ((1 + tthr) * qsig)%r * p_max dcmt) 0 qsig.
proof.
fel 30 Cnt.cs (fun _ => ((1 + tthr) * qsig)%r * p_max dcmt) qsig Bd.b2
    [CntO(SOA2).o1 : true; CntO(SOA2).o2 : true; CntO(SOA2).o3 : true;
     CntH(HOL(H0H.LC)).h0 : false; CntH(HOL(H0H.LC)).h1 : false; CntH(HOL(H0H.LC)).hc : false;
     H0H.LC.gf : false]
    (b2inv S.toks S.req S.lr Cnt.cs).
+ done.
+ smt().
+ inline *; auto; call (_ : true); auto => />.
  by rewrite /b2inv fdom0 fcards0 => *; smt(mem_empty).
+ proc; inline SOA2.o1; sp; if; last by hoare; [smt(pmax_ge0 ge0_qsig thr_range) | auto].
  wp; rnd (fun c => dupc S.toks c \/ seenc S.lr c); skip => &h /> cs1 hcs0 hcs1 hb hinv hi1 hi2 hic.
  move: hinv; rewrite /b2inv => -[hc [hl [hv _]]].
  apply (StdOrder.RealOrder.ler_trans (((1 + tthr) * cs1)%r * p_max dcmt)); first by apply fresh_cmt.
  apply StdOrder.RealOrder.ler_wpmul2r; first exact pmax_ge0.
  by rewrite le_fromint; smt(thr_range).
+ move=> c; proc; inline SOA2.o1; sp; if; last by auto => />; rewrite /b2inv; smt().
  auto => /> &h hinv hi1 hi2 hic y _.
  move: hinv; rewrite /b2inv => -[hc [hl [hv ht]]].
  rewrite fdom_set fcardU1; do !split; [smt() | smt() | smt() | exact hv |].
  move=> u; rewrite mem_set get_setE; case: (u = S.ctr{h}) => [-> /= | hne /=] //.
  exact (ht u).
+ by move=> b c; conseq (_ : false ==> _) => //.
+ hoare; first smt(pmax_ge0 ge0_qsig thr_range).
  by proc; inline SOA2.o2; sp; if; [sp; if; [inline *; sp; if; auto | auto] | auto].
+ move=> c; proc; inline SOA2.o2; sp; if; last by auto => />; rewrite /b2inv; smt().
  sp; if; last by auto => />; rewrite /b2inv; smt().
  inline *; sp; if; auto => /> &h hinv hu hph huq hsz hin hiT hcs hown.
  + move=> hsv s0 _.
    move: hinv; rewrite /b2inv => -[hc [hl [hv ht]]].
    rewrite fdom_set fcardU1 mem_fdom hu /=; do !split; [smt() | smt() | smt() | exact hv |].
    move=> w; rewrite !mem_set !get_setE; case: (w = u{h}) => [-> /= | hne /= hw] //; first smt().
    exact (ht w hw).
  + move=> hsv.
    move: hinv; rewrite /b2inv => -[hc [hl [hv ht]]].
    rewrite fdom_set fcardU1 mem_fdom hu /=; do !split; [smt() | smt() | smt() | exact hv |].
    move=> w; rewrite !mem_set !get_setE; case: (w = u{h}) => [-> /= | hne /= hw] //; first smt().
    exact (ht w hw).
+ by move=> b c; conseq (_ : false ==> _) => //.
+ hoare; first smt(pmax_ge0 ge0_qsig thr_range).
  proc; inline SOA2.o3; sp; if; last by auto.
  sp; if; last by auto.
  sp; if; last by auto.
  seq 3 : (!Bd.b2); first by auto.
  seq 1 : (!Bd.b2).
  + while (!Bd.b2); last by auto.
    wp; call (_ : true); last by auto.
    by sp; if; [auto | inline *; sp; if; [sp; if; auto | auto]].
  if; last by auto.
  seq 6 : (!Bd.b2); first by while (!Bd.b2); auto.
  by sp; if; [auto | if; auto].
+ move=> c; proc; inline SOA2.o3; sp; if; last by auto => />; rewrite /b2inv; smt().
  sp; if; last by auto => />; rewrite /b2inv; smt().
  sp; if; last by auto => />; rewrite /b2inv; smt().
  seq 3 : (c < Cnt.cs /\ b2inv S.toks S.req S.lr (Cnt.cs - 1) /\ u0 \in S.toks /\ tok = oget S.toks.[u0]
           /\ tok.`tk_phase = 2).
  + by auto => />; rewrite /b2inv; smt().
  seq 1 : (c < Cnt.cs /\ b2inv S.toks S.req S.lr (Cnt.cs - 1) /\ u0 \in S.toks /\ tok = oget S.toks.[u0]
           /\ tok.`tk_phase = 2).
  + while (c < Cnt.cs /\ b2inv S.toks S.req S.lr (Cnt.cs - 1) /\ u0 \in S.toks /\ tok = oget S.toks.[u0]
           /\ tok.`tk_phase = 2); last by auto.
    wp; call (_ : true); last by auto.
    by sp; if; [auto | inline *; sp; if; [sp; if; auto | auto]].
  if; last by auto => />; rewrite /b2inv; smt().
  seq 6 : (c < Cnt.cs /\ b2inv S.toks S.req S.lr (Cnt.cs - 1) /\ u0 \in S.toks /\ tok = oget S.toks.[u0]
           /\ tok.`tk_phase = 2).
  + by while (c < Cnt.cs /\ b2inv S.toks S.req S.lr (Cnt.cs - 1) /\ u0 \in S.toks
              /\ tok = oget S.toks.[u0] /\ tok.`tk_phase = 2); auto.
  sp; if; [auto | if; auto] => /> &h hc0 hinv hu hph *;
    (move: hinv; rewrite /b2inv => -[hc [hl [hv ht]]];
     rewrite fdom_set fcardU1 mem_fdom hu /=; do !split; [smt() | smt() | | ]); smt(mem_set get_setE).
+ by move=> b c; conseq (_ : false ==> _) => //.
qed.

(* A fresh first message equals an existing one with probability at most
   qsig ((1 + tthr) qsig) p_max(dcmt) *)
lemma ga_b2 &m :
  Pr[H0H.LCG(BA(A)).main(true) @ &m : Bd.b2] <= qsig%r * (((1 + tthr) * qsig)%r * p_max dcmt).
proof.
have -> := ga_gaf A &m (fun _ _ _ b2 _ _ _ _ _ => b2).
have -> := gaf_gag A &m (fun _ _ _ b2 _ _ _ _ _ => b2).
have h1 := gag_b2_fel &m.
have h0 : Pr[GAg(A).main() @ &m : Bd.b2 /\ !(Cnt.cs <= qsig)] = 0%r.
+ by byphoare => //; hoare; conseq gag_bnd => /#.
have hs : bigi predT (fun _ => ((1 + tthr) * qsig)%r * p_max dcmt) 0 qsig
          = qsig%r * (((1 + tthr) * qsig)%r * p_max dcmt).
+ by rewrite sumri_const; smt(ge0_qsig).
rewrite Pr[mu_split (Cnt.cs <= qsig)] h0 /=.
smt().
qed.

end section B2.
