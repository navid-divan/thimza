require import AllCore Int List Distr DList FMap FSet Real RealExp Finite StdOrder StdBigop FelTactic.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption.
require import Protocol Notions Privacy Extract FinEnum ChainBase ChainGame ChainCol ChainSim.
require import ChainDead ChainLazy ChainFlag ChainGA ChainB1a ChainB1b ChainB1c.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.
import Bigreal.BRA.

(* ---------- the probability of a logged opening point in the lazy game ----------

   In the instrumented lazy replay LEf, the flag badE is raised only when a fresh nonce hits a
   logged point of its token.  Every signing query and every final reveal increments Cnt.cs, which
   ends below 2 qsig, and when Cnt.cs = c each token has at most c logged points (a check logs one
   point for each phase one token of each honest member of its committee, and committees have
   distinct members).  The failure event lemma then bounds badE by the sum of c pw for c < 2 qsig. *)

(* The commitments stay lazy, requests of second-round tokens have distinct members, and each
   token has at most as many logged points as signing queries so far *)
op [opaque] cinvE (toks : (int, token) fmap) (log : (h0in * int) list) (cs : int) (lft : bool) : bool =
  lft
  /\ (forall u, u \in toks => (oget toks.[u]).`tk_phase = 2 => uniq (oget toks.[u]).`tk_T)
  /\ (forall w, size (lpts log w) <= cs).

lemma lpts_cat (l1 l2 : (h0in * int) list) w : lpts (l1 ++ l2) w = lpts l1 w ++ lpts l2 w.
proof. by rewrite /lpts filter_cat map_cat. qed.

lemma lpts_new (x : h0in) (L : int list) w :
  size (lpts (map (fun w' => (x, w')) L) w) = count (pred1 w) L.
proof. by rewrite /lpts size_map filter_map size_map size_filter; apply eq_count => v. qed.

lemma count_predI_le ['a] (p q : 'a -> bool) s : count (predI p q) s <= count p s.
proof. by elim: s => //= x s ih; rewrite /predI; smt(). qed.

lemma lpts_add log (x : h0in) (P : int -> bool) (toks : (int, token) fmap) w :
  size (lpts (log ++ map (fun w' => (x, w')) (filter P (elems (fdom toks)))) w)
  <= size (lpts log w) + b2i (P w).
proof.
rewrite lpts_cat size_cat lpts_new count_filter.
case: (P w) => hp.
+ have := count_uniq_mem (elems (fdom toks)) w (uniq_elems (fdom toks)).
  have : count (predI (pred1 w) P) (elems (fdom toks)) <= count (pred1 w) (elems (fdom toks)).
  - exact count_predI_le.
  smt().
have -> : count (predI (pred1 w) P) (elems (fdom toks)) = 0.
- by rewrite -(count_pred0 (elems (fdom toks))); apply eq_count => v; rewrite /predI /pred1 /pred0; smt().
smt().
qed.

lemma lpts_step (log : (h0in * int) list) (toks : (int, token) fmap) (x : h0in) (T : int list)
                (k c0 : int) :
  0 <= k < size T =>
  (forall w, size (lpts log w) <= c0 + count (pred1 (oget toks.[w]).`tk_i) (take k T)) =>
  forall w,
    size (lpts (log ++ map (fun w' => (x, w'))
                       (filter (fun w' => (oget toks.[w']).`tk_phase = 1 /\ (oget toks.[w']).`tk_i = nth 0 T k)
                               (elems (fdom toks)))) w)
    <= c0 + count (pred1 (oget toks.[w]).`tk_i) (take (k + 1) T).
proof.
move=> hk hi w.
have h1 := lpts_add log x (fun w' => (oget toks.[w']).`tk_phase = 1 /\ (oget toks.[w']).`tk_i = nth 0 T k) toks w.
rewrite (take_nth 0 k T hk) -cats1 count_cat /=.
have := hi w.
smt().
qed.

lemma lpts_skip (log : (h0in * int) list) (toks : (int, token) fmap) (T : int list) (k c0 : int) :
  0 <= k < size T =>
  (forall w, size (lpts log w) <= c0 + count (pred1 (oget toks.[w]).`tk_i) (take k T)) =>
  forall w, size (lpts log w) <= c0 + count (pred1 (oget toks.[w]).`tk_i) (take (k + 1) T).
proof.
move=> hk hi w; rewrite (take_nth 0 k T hk) -cats1 count_cat /=.
have := hi w; smt().
qed.

lemma lpts_end (log : (h0in * int) list) (toks : (int, token) fmap) (T : int list) (k c0 : int) :
  uniq T => size T <= k =>
  (forall w, size (lpts log w) <= c0 + count (pred1 (oget toks.[w]).`tk_i) (take k T)) =>
  forall w, size (lpts log w) <= c0 + 1.
proof.
move=> hu hk hi w; have := hi w; rewrite take_oversize // count_uniq_mem //.
smt().
qed.

section B1d.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -Fz, -Bd, -Lg1, -Bx, -Lc0, -H0H.QRO, -H0C.QRO,
                         -H1O.QRO, -HCO.QRO, -H0H.LC, -H0H.CQ}.

declare axiom A_bnd (H <: HOr {-A, -Cnt}) (O <: SOr {-A, -Cnt}) :
  hoare [A(CntH(H), CntO(O)).forge : Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 ==>
         Cnt.c0 <= qh0 /\ Cnt.c1 <= qh1 /\ Cnt.cc <= qhc /\ Cnt.cs <= qsig].

declare axiom reg_open :
  forall (w : row), mu (dnonce `*` dnoiser) (fun (s : vec * row) => rndc (commit s.`1 s.`2) = w) <= pw.

lemma ge0_pw : 0%r <= pw.
proof. by have := reg_open witness; smt(mu_bounded). qed.

lemma rev_ph c :
  phoare [Fin(LCI).rev : Cnt.cs = c /\ !Bx.badE /\ cinvE S.toks Lg1.log Cnt.cs H0H.LC.lft /\ 0 <= c
          ==> Bx.badE] <= (c%r * pw).
proof.
proc; inline *; wp; sp; if; last by hoare; [smt(ge0_pw) | auto => /> /#].
wp; rnd (fun (s : vec * row) => popn s \in lpts Lg1.log u1); skip => /> &h hb hinv hc hu.
apply (StdOrder.RealOrder.ler_trans ((size (lpts Lg1.log{h} u{h}))%r * pw)); first by apply (pmem _ reg_open).
apply StdOrder.RealOrder.ler_wpmul2r; first exact ge0_pw.
by rewrite le_fromint; move: hinv; rewrite /cinvE => -[_ [_ h]]; apply h.
qed.

lemma o2_ph c :
  phoare [CntO(BXO(LCI)).o2 : Cnt.cs = c /\ !Bx.badE /\ cinvE S.toks Lg1.log Cnt.cs H0H.LC.lft /\ 0 <= c
          ==> Bx.badE] <= (c%r * pw).
proof.
proc; inline *; sp; if; last by hoare; [smt(ge0_pw) | auto => /> /#].
sp; if; last by hoare; [smt(ge0_pw) | auto => /> /#].
wp; sp; if; last by hoare; [smt(ge0_pw) | auto => /> /#].
wp; rnd (fun (s : vec * row) => popn s \in lpts Lg1.log u2); skip => /> &h hb hinv hc *.
apply (StdOrder.RealOrder.ler_trans ((size (lpts Lg1.log{h} u{h}))%r * pw)); first by apply (pmem _ reg_open).
apply StdOrder.RealOrder.ler_wpmul2r; first exact ge0_pw.
by rewrite le_fromint; move: hinv; rewrite /cinvE => -[_ [_ h]]; apply h.
qed.

lemma lef_fel &m :
  Pr[LEf(A).main() @ &m : Bx.badE /\ Cnt.cs <= 2 * qsig]
  <= bigi predT (fun c => c%r * pw) 0 (2 * qsig).
proof.
fel 34 Cnt.cs (fun c => c%r * pw) (2 * qsig) Bx.badE
    [CntO(BXO(LCI)).o1 : true; CntO(BXO(LCI)).o2 : true; CntO(BXO(LCI)).o3 : true;
     Fin(LCI).rev : true]
    (cinvE S.toks Lg1.log Cnt.cs H0H.LC.lft).
+ done.
+ by move=> &m0 [].
+ inline *; auto; call (_ : true); auto => />.
  by rewrite /cinvE /lpts /=; smt(mem_empty).
(* final reveals *)
+ exlim Cnt.cs => c0; conseq (rev_ph c0) => /#.
+ move=> c; proc; inline *; sp; if; auto => /> &h; rewrite /cinvE => /> *; smt().
+ by move=> b c; conseq (_ : false ==> _) => //.
(* first round *)
+ hoare; first by smt(ge0_pw).
  conseq (_ : !Bx.badE /\ H0H.LC.lft ==> !Bx.badE); first by move=> &h; rewrite /cinvE /#.
  proc; inline *; sp; if; last by auto.
  rcondt 3; first by auto.
  by sp; if; auto.
+ move=> c; proc; inline *; sp; if; last by auto; rewrite /cinvE; smt().
  rcondt 3; first by auto; rewrite /cinvE; smt().
  sp; if; auto; rewrite /cinvE; smt(mem_set get_setE).
+ by move=> b c; conseq (_ : false ==> _) => //.
(* second round *)
+ exlim Cnt.cs => c0; conseq (o2_ph c0) => /#.
+ move=> c; proc; inline *; sp; if; last by auto; rewrite /cinvE; smt().
  sp; if; last by auto; rewrite /cinvE; smt().
  sp; if; auto; rewrite /cinvE /ok2 /=; smt(mem_set get_setE).
+ by move=> b c; conseq (_ : false ==> _) => //.
(* third round *)
+ hoare; first by smt(ge0_pw).
  proc; inline BXO(LCI).o3; sp; if; last by auto.
  sp; if; last by auto.
  sp; if; last by auto.
  seq 3 : (!Bx.badE); first by auto.
  seq 1 : (!Bx.badE).
  + while (!Bx.badE); last by auto.
    by wp; call h0any_t; auto.
  if; last by auto.
  seq 6 : (!Bx.badE); first by while (!Bx.badE); auto.
  by sp; if; [auto | if; auto].
+ move=> c; proc; inline BXO(LCI).o3; sp; if; last by auto; rewrite /cinvE; smt().
  sp; if; last by auto; rewrite /cinvE; smt().
  sp; if; last by auto; rewrite /cinvE; smt().
  seq 3 : (c + 1 = Cnt.cs /\ H0H.LC.lft
           /\ (forall u, u \in S.toks => (oget S.toks.[u]).`tk_phase = 2 => uniq (oget S.toks.[u]).`tk_T)
           /\ (forall w, size (lpts Lg1.log w) <= c + count (pred1 (oget S.toks.[w]).`tk_i) (take k T0))
           /\ k = 0 /\ u0 \in S.toks /\ tok = oget S.toks.[u0] /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T
           /\ uniq T0).
  + auto; rewrite /cinvE => &h /> *; smt(take0).
  seq 1 : (c + 1 = Cnt.cs /\ H0H.LC.lft
           /\ (forall u, u \in S.toks => (oget S.toks.[u]).`tk_phase = 2 => uniq (oget S.toks.[u]).`tk_T)
           /\ (forall w, size (lpts Lg1.log w) <= c + 1)
           /\ u0 \in S.toks /\ tok = oget S.toks.[u0] /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T).
  + while (c + 1 = Cnt.cs /\ H0H.LC.lft
           /\ (forall u, u \in S.toks => (oget S.toks.[u]).`tk_phase = 2 => uniq (oget S.toks.[u]).`tk_T)
           /\ (forall w, size (lpts Lg1.log w) <= c + count (pred1 (oget S.toks.[w]).`tk_i) (take k T0))
           /\ 0 <= k /\ u0 \in S.toks /\ tok = oget S.toks.[u0] /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T
           /\ uniq T0).
    - wp; call h0any_t; auto => /> &h hl hu hlog hk hu0 hph huq hkT.
      split => _; (split; last smt()).
      + by apply (lpts_step _ _ _ _ _ _ _ hlog); smt().
      by apply (lpts_skip _ _ _ _ _ _ hlog); smt().
    auto => /> &h hl hu hlog hu0 hph huq log k0 hk hlog' hk0.
    by apply (lpts_end _ _ _ _ _ huq _ hlog'); smt().
  if; last by auto; rewrite /cinvE; smt().
  seq 6 : (c + 1 = Cnt.cs /\ H0H.LC.lft
           /\ (forall u, u \in S.toks => (oget S.toks.[u]).`tk_phase = 2 => uniq (oget S.toks.[u]).`tk_T)
           /\ (forall w, size (lpts Lg1.log w) <= c + 1)
           /\ u0 \in S.toks /\ tok = oget S.toks.[u0] /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T).
  + by while (c + 1 = Cnt.cs /\ H0H.LC.lft
           /\ (forall u, u \in S.toks => (oget S.toks.[u]).`tk_phase = 2 => uniq (oget S.toks.[u]).`tk_T)
           /\ (forall w, size (lpts Lg1.log w) <= c + 1)
           /\ u0 \in S.toks /\ tok = oget S.toks.[u0] /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T); auto.
  sp; if; [auto | if; auto]; rewrite /cinvE /erase /=; smt(mem_set get_setE).
+ by move=> b c; conseq (_ : false ==> _) => //.
qed.


(* The signing queries and the final reveals stay below 2 qsig *)
local lemma forge_bnd :
  hoare [A(CntH(HOL(LCI)), CntO(BXO(LCI))).forge :
    card (fdom S.toks) <= Cnt.cs /\ Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 ==>
    card (fdom S.toks) <= Cnt.cs /\ Cnt.cs <= qsig].
proof.
conseq (A_bnd (HOL(LCI)) (BXO(LCI))) (_ : card (fdom S.toks) <= Cnt.cs ==> card (fdom S.toks) <= Cnt.cs) => //.
proc (card (fdom S.toks) <= Cnt.cs) => //.
+ proc; inline *; sp; if; last by auto => /> /#.
  by sp; if; [sp; if; auto | sp; if; auto]; smt(fdom_set fcardU1).
+ proc; inline BXO(LCI).o2; sp; if; last by auto => /> /#.
  sp; if; last by auto => /> /#.
  by inline *; sp; if; auto => /> *; rewrite fdom_set fcardU1 mem_fdom; smt().
+ proc; inline BXO(LCI).o3; sp; if; last by auto => /> /#.
  sp; if; last by auto => /> /#.
  sp; if; last by auto => /> /#.
  seq 3 : (card (fdom S.toks) < Cnt.cs /\ u0 \in S.toks); first by auto => /> /#.
  seq 1 : (card (fdom S.toks) < Cnt.cs /\ u0 \in S.toks).
  + by while (card (fdom S.toks) < Cnt.cs /\ u0 \in S.toks); [wp; call h0any_t; auto | auto].
  if; last by auto => /> /#.
  seq 6 : (card (fdom S.toks) < Cnt.cs /\ u0 \in S.toks).
  + by while (card (fdom S.toks) < Cnt.cs /\ u0 \in S.toks); auto.
  by sp; if; [auto | if; auto]; smt(fdom_set fcardU1 mem_fdom).
+ by proc; inline *; sp; if; [auto | sp; if; [sp; if; auto | auto]].
+ by proc; inline *; auto.
by proc; inline *; auto.
qed.

lemma ph1_size (toks : (int, token) fmap) :
  size (filter (fun u => (oget toks.[u]).`tk_phase = 1) (elems (fdom toks))) <= card (fdom toks).
proof. by rewrite size_filter cardE count_size. qed.

lemma lef_bnd : hoare [LEf(A).main : true ==> Cnt.cs <= 2 * qsig].
proof.
proc.
seq 34 : (card (fdom S.toks) <= Cnt.cs /\ Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0).
+ by auto; call (_ : true); inline *; auto => />; smt(fdom0 fcards0).
seq 1 : (card (fdom S.toks) <= Cnt.cs /\ Cnt.cs <= qsig); first by call forge_bnd.
wp; while (Cnt.cs + (size us - k) <= 2 * qsig /\ k <= size us).
+ by inline *; sp; if; auto => /> /#.
auto => /> &h hc hq; have := ph1_size S.toks{h}; smt(size_ge0).
qed.

(* A logged opening point is hit with probability at most qsig (2 qsig - 1) pw *)
lemma lef_badE &m :
  Pr[LEf(A).main() @ &m : Bx.badE] <= (qsig * (2 * qsig - 1))%r * pw.
proof.
have h1 := lef_fel &m.
have h0 : Pr[LEf(A).main() @ &m : Bx.badE /\ !(Cnt.cs <= 2 * qsig)] = 0%r.
+ by byphoare => //; hoare; conseq lef_bnd => /#.
have hs : bigi predT (fun c => c%r * pw) 0 (2 * qsig) = (qsig * (2 * qsig - 1))%r * pw.
+ rewrite -mulr_suml Bigreal.sumidE; first smt(ge0_qsig).
  by congr; rewrite fromintM; field.
rewrite Pr[mu_split (Cnt.cs <= 2 * qsig)] h0 /=.
smt().
qed.

lemma ept_bound &m :
  Pr[H0H.LCG(BBX(A)).main(true) @ &m : Lg1.ept] <= (qsig * (2 * qsig - 1))%r * pw.
proof.
rewrite (bbx_lef A &m).
have h0 : Pr[LEf(A).main() @ &m : Lg1.ept /\ !Bx.badE] = 0%r.
+ by byphoare => //; hoare; conseq (lef_ept A) => /#.
have h1 : Pr[LEf(A).main() @ &m : Lg1.ept /\ Bx.badE] <= Pr[LEf(A).main() @ &m : Bx.badE].
+ by rewrite Pr[mu_sub].
rewrite Pr[mu_split Bx.badE] h0 /=.
smt(lef_badE).
qed.

(* The first flag: transport to eager commitments, a collision there, or a logged point *)
lemma bbx_split &m :
  Pr[H0H.LCG(BBX(A)).main(true) @ &m : Bd.b1]
  <= Pr[H0H.LCG(BBX(A)).main(true) @ &m : res] + Pr[H0H.LCG(BBX(A)).main(true) @ &m : Lg1.ept].
proof.
rewrite Pr[mu_split Lg1.ept].
have h1 : Pr[H0H.LCG(BBX(A)).main(true) @ &m : Bd.b1 /\ Lg1.ept]
          <= Pr[H0H.LCG(BBX(A)).main(true) @ &m : Lg1.ept].
+ by rewrite Pr[mu_sub].
have h2 : Pr[H0H.LCG(BBX(A)).main(true) @ &m : Bd.b1 /\ !Lg1.ept]
          <= Pr[H0H.LCG(BBX(A)).main(true) @ &m : res].
+ byequiv => //; proc; inline BBX(A, H0H.LC).main; wp.
  conseq (_ : _ ==> ={Bd.b1, Lg1.log, Lg1.sec}) => //.
  by sim.
smt().
qed.

lemma ga_b1 &m :
  Pr[H0H.LCG(BA(A)).main(true) @ &m : Bd.b1]
  <= 2%r * (qh0 + tthr * qsig)%r * sqrt (qsig%r * pw) + (qsig * qsig)%r * pw
     + 27%r * (qh0 + (1 + tthr) * qsig + 2)%r ^ 3 * p_max dcmt
     + (qsig * (2 * qsig - 1))%r * pw.
proof.
rewrite (ga_bbx A &m).
have h1 := bbx_split &m.
have h2 := bbx_o2h A A_bnd reg_open &m.
have h3 := bbx_b1col A A_bnd &m.
have h4 := ept_bound &m.
smt().
qed.

end section B1d.
