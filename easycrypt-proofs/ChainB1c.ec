require import AllCore Int List Distr DList FMap FSet Real RealExp Finite StdOrder StdBigop FelTactic.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption.
require import Protocol Notions Privacy Extract FinEnum ChainBase ChainGame ChainCol ChainSim.
require import ChainDead ChainLazy ChainFlag ChainGA ChainB1a.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.
import Bigreal.BRA.

(* ---------- the logged opening points in the lazy game ----------

   With lazy commitments the nonce of a token is sampled when the token is revealed, after all
   the checks that logged the token (logged tokens are unopened, hence unrevealed).  The lazy
   commitment oracle is instrumented to raise a flag when a sampled nonce hits a logged point of
   its token; a logged opening point at the end raises this flag, and each sampling raises it
   with probability at most (the number of logged points of the token) pw. *)

module Bx = {
  var badE : bool
}.

(* The points logged for a token *)
op lpts (log : (h0in * int) list) (u : int) : row list =
  map (fun (e : h0in * int) => e.`1.`2) (filter (fun (e : h0in * int) => e.`2 = u) log).

module LCI = {
  proc gsec(u : int) : vec * row = {
    var s;
    if (u \notin H0H.LC.sv) {
      s <$ dnonce `*` dnoiser;
      Bx.badE <- Bx.badE \/ popn s \in lpts Lg1.log u;
      H0H.LC.sv.[u] <- s;
    }
    return oget H0H.LC.sv.[u];
  }

  proc gf = H0H.LC.gf

  proc h(x : h0key * row) : cmt = {
    var r, us;
    H0H.CQ.n <- H0H.CQ.n + 1;
    us <- filter (fun u => u \in H0H.LC.sv /\ rndc (commit (oget H0H.LC.sv.[u]).`1 (oget H0H.LC.sv.[u]).`2) = x.`2)
                 H0H.LC.rv;
    if (H0H.LC.lft /\ us <> []) {
      r <@ gf(head 0 us, x.`1);
    } else {
      r <- H0H.QRO.fh x;
    }
    return r;
  }

  proc commit(u : int, k : h0key) : cmt = {
    var r, s;
    if (H0H.LC.lft) {
      r <@ gf(u, k);
    } else {
      s <@ gsec(u);
      r <- H0H.QRO.fh (k, rndc (commit s.`1 s.`2));
    }
    return r;
  }

  proc reveal(u : int) : vec * row = {
    var s;
    s <@ gsec(u);
    if (!(u \in H0H.LC.rv)) { H0H.LC.rv <- u :: H0H.LC.rv; }
    return s;
  }
}.

(* The lazy replay with the instrumented oracle, as one procedure *)
module LEf (A : Adv) = {
  proc main() : bool = {
    var b, us, k, mu, sg, ok, sks, sds;
    H0H.QRO.init();
    H0H.LC.sv <- empty;
    H0H.LC.rv <- [];
    H0H.LC.fv <- empty;
    H0H.LC.lft <- true;
    H0H.CQ.n <- 0;
    Bx.badE <- false;
    H0C.QRO.init();
    H1O.QRO.init();
    HCO.QRO.init();
    Lg1.log <- [];
    Lg1.sec <- empty;
    Lg1.ept <- false;
    S.cs <@ A(CntH(HOL(LCI)), CntO(BXO(LCI))).corrupt();
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
    (mu, sg) <@ A(CntH(HOL(LCI)), CntO(BXO(LCI))).forge(S.t, sks, sds);
    ok <- verify (hcof HCO.QRO.fh) S.t mu sg /\ admc S.cs;
    b <- win4 S.cs S.lo mu ok;
    us <- filter (fun u => (oget S.toks.[u]).`tk_phase = 1) (elems (fdom S.toks));
    k <- 0;
    while (k < size us) {
      Fin(LCI).rev(nth 0 us k);
      k <- k + 1;
    }
    Lg1.ept <- eptof Lg1.log Lg1.sec;
    return Bd.b1 /\ !Lg1.ept;
  }
}.

(* A fresh nonce hits one of given points with probability at most their number times pw *)
lemma pmem (X : row list) :
  (forall (w : row), mu (dnonce `*` dnoiser) (fun (s : vec * row) => rndc (commit s.`1 s.`2) = w) <= pw) =>
  mu (dnonce `*` dnoiser) (fun (s : vec * row) => popn s \in X) <= (size X)%r * pw.
proof.
move=> hreg; elim: X => [| y X ih].
+ by rewrite (mu_eq _ _ pred0) // mu0.
rewrite (mu_eq _ _ (predU (fun (s : vec * row) => rndc (commit s.`1 s.`2) = y)
                          (fun (s : vec * row) => popn s \in X))).
+ by move=> s; rewrite /predU /popn in_cons.
rewrite mu_or /=.
have := hreg y.
have := mu_bounded (dnonce `*` dnoiser) (predI (fun (s : vec * row) => rndc (commit s.`1 s.`2) = y)
                                               (fun (s : vec * row) => popn s \in X)).
smt().
qed.

(* The instrumented lazy run: a logged point of a revealed token that equals its opening raised
   the flag, unopened tokens are unrevealed, recorded nonces are the nonces, revealed tokens
   exist, and tokens are below the counter *)
op [opaque] einv (toks : (int, token) fmap) (sv sec : (int, vec * row) fmap) (log : (h0in * int) list)
                 (ctr : int) (badE lft : bool) : bool =
  (forall (e : h0in * int), e \in log => e.`2 \notin sv \/ (popn (oget sv.[e.`2]) = e.`1.`2 => badE))
  /\ (forall u, u \in toks => (oget toks.[u]).`tk_phase = 1 => u \notin sv)
  /\ (forall u, u \in sec => u \in sv /\ oget sec.[u] = oget sv.[u])
  /\ (forall u, u \in sv => u \in toks)
  /\ (forall u, u \in toks => u < ctr)
  /\ lft.

(* A sampled nonce keeps the logged points flagged *)
lemma lpts_mem (log : (h0in * int) list) (e : h0in * int) :
  e \in log => e.`1.`2 \in lpts log e.`2.
proof. by move=> he; rewrite /lpts; apply (map_f (fun (e : h0in * int) => e.`1.`2)); rewrite List.mem_filter. qed.

lemma h0_e : hoare [CntH(HOL(LCI)).h0 : einv S.toks H0H.LC.sv Lg1.sec Lg1.log S.ctr Bx.badE H0H.LC.lft ==> einv S.toks H0H.LC.sv Lg1.sec Lg1.log S.ctr Bx.badE H0H.LC.lft].
proof. by proc; inline *; sp; if; [auto | sp; if; [sp; if; auto | auto]]. qed.

lemma h1_e : hoare [CntH(HOL(LCI)).h1 : einv S.toks H0H.LC.sv Lg1.sec Lg1.log S.ctr Bx.badE H0H.LC.lft ==> einv S.toks H0H.LC.sv Lg1.sec Lg1.log S.ctr Bx.badE H0H.LC.lft].
proof. by proc; inline *; auto. qed.

lemma hc_e : hoare [CntH(HOL(LCI)).hc : einv S.toks H0H.LC.sv Lg1.sec Lg1.log S.ctr Bx.badE H0H.LC.lft ==> einv S.toks H0H.LC.sv Lg1.sec Lg1.log S.ctr Bx.badE H0H.LC.lft].
proof. by proc; inline *; auto. qed.

lemma o1_e : hoare [CntO(BXO(LCI)).o1 : einv S.toks H0H.LC.sv Lg1.sec Lg1.log S.ctr Bx.badE H0H.LC.lft ==> einv S.toks H0H.LC.sv Lg1.sec Lg1.log S.ctr Bx.badE H0H.LC.lft].
proof.
proc; inline BXO(LCI).o1; sp; if; last by auto.
inline *; sp; if; last by sp; if; auto; rewrite /einv => &h />; smt().
sp; if; auto => /> &h; rewrite /einv => -[#] h1 h2 h3 h4 h5 h6 *;
  (do !split => //; [ move=> w; rewrite mem_set get_setE; case: (w = S.ctr{h}) => [-> /= | hne /= hw];
                        [smt() | exact (h2 w hw)]
                    | by move=> w /h4 hw; rewrite mem_set hw
                    | by move=> w; rewrite mem_set => -[/h5 | ->]; smt() ]).
qed.

lemma o2_e : hoare [CntO(BXO(LCI)).o2 : einv S.toks H0H.LC.sv Lg1.sec Lg1.log S.ctr Bx.badE H0H.LC.lft ==> einv S.toks H0H.LC.sv Lg1.sec Lg1.log S.ctr Bx.badE H0H.LC.lft].
proof.
proc; inline BXO(LCI).o2; sp; if; last by auto.
sp; if; last by auto.
inline *; sp; if; last by auto => /> &h; rewrite /einv => -[#] h1 h2 *; smt().
auto => /> &h; rewrite /einv => -[#] h1 h2 h3 h4 h5 h6 hu hph *.
do !split => //.
- move=> e he; rewrite mem_set get_setE; case: (e.`2 = u{h}) => [heq | hne] /=.
  + by move=> hp; right; rewrite hp -heq; apply lpts_mem.
  by case: (h1 e he) => [hn | hb]; [left | right => /hb ->].
- move=> w; rewrite mem_set get_setE; case: (w = u{h}) => [-> /= | hne /= hw hph']; first done.
  by rewrite mem_set hne /=; apply h2.
- move=> w; rewrite mem_set get_setE; case: (w = u{h}) => [-> /= | hne /= hw]; first by rewrite mem_set.
  by have [hs hv] := h3 w hw; rewrite mem_set hs get_setE hne.
- by move=> w; rewrite mem_set => -[/h4 hw | ->]; rewrite mem_set; [left | left].
by move=> w; rewrite mem_set => -[/h5 | -> /=]; [done | smt()].
qed.

lemma einv_log toks sv sec log ctr badE lft (x : h0in) (j : int) :
  einv toks sv sec log ctr badE lft =>
  einv toks sv sec
       (log ++ map (fun w => (x, w))
                   (filter (fun w => (oget toks.[w]).`tk_phase = 1 /\ (oget toks.[w]).`tk_i = j)
                           (elems (fdom toks)))) ctr badE lft.
proof.
rewrite /einv => -[#] h1 h2 h3 h4 h5 h6; do !split => //.
move=> e; rewrite mem_cat => -[he | /mapP [w [hw ->]]]; first exact (h1 e he).
move: hw; rewrite List.mem_filter /= -memE mem_fdom => -[[hph _] hw].
by left; apply (h2 w hw hph).
qed.

lemma einv_erase toks sv sec log ctr badE lft (u : int) :
  einv toks sv sec log ctr badE lft => u \in toks =>
  einv toks.[u <- erase (oget toks.[u])] sv sec log ctr badE lft.
proof.
rewrite /einv => -[#] h1 h2 h3 h4 h5 h6 hu; do !split => //.
- move=> w; rewrite mem_set get_setE; case: (w = u) => [-> /= | hne /= hw]; first by rewrite /erase.
  exact (h2 w hw).
- by move=> w /h4 hw; rewrite mem_set hw.
by move=> w; rewrite mem_set => -[/h5 // | ->]; apply h5.
qed.

lemma h0any_t : hoare [SOA(LCI).h0any : true ==> true].
proof. by proc; inline *; sp; if; [auto | sp; if; [sp; if; auto | auto]]. qed.

lemma o3_e : hoare [CntO(BXO(LCI)).o3 : einv S.toks H0H.LC.sv Lg1.sec Lg1.log S.ctr Bx.badE H0H.LC.lft ==> einv S.toks H0H.LC.sv Lg1.sec Lg1.log S.ctr Bx.badE H0H.LC.lft].
proof.
proc; inline BXO(LCI).o3; sp; if; last by auto.
sp; if; last by auto.
sp; if; last by auto.
seq 3 : (einv S.toks H0H.LC.sv Lg1.sec Lg1.log S.ctr Bx.badE H0H.LC.lft /\ u0 \in S.toks /\ tok = oget S.toks.[u0]); first by auto.
seq 1 : (einv S.toks H0H.LC.sv Lg1.sec Lg1.log S.ctr Bx.badE H0H.LC.lft /\ u0 \in S.toks /\ tok = oget S.toks.[u0]).
+ while (einv S.toks H0H.LC.sv Lg1.sec Lg1.log S.ctr Bx.badE H0H.LC.lft /\ u0 \in S.toks /\ tok = oget S.toks.[u0]); last by auto.
  wp; call h0any_t; auto => /> &h hi hu _.
  by case: (nth 0 T0{h} k{h} \in S.cs{h}) => _ //=; apply einv_log.
if; last by auto.
seq 6 : (einv S.toks H0H.LC.sv Lg1.sec Lg1.log S.ctr Bx.badE H0H.LC.lft /\ u0 \in S.toks /\ tok = oget S.toks.[u0]); first by while (einv S.toks H0H.LC.sv Lg1.sec Lg1.log S.ctr Bx.badE H0H.LC.lft /\ u0 \in S.toks /\ tok = oget S.toks.[u0]); auto.
by sp; if; [auto | if; auto] => /> &h hi hu *; apply einv_erase.
qed.

(* The final reveals: logged points flagged and recorded nonces as before *)
op [opaque] finv (sv sec : (int, vec * row) fmap) (log : (h0in * int) list) (badE : bool) : bool =
  (forall (e : h0in * int), e \in log => e.`2 \notin sv \/ (popn (oget sv.[e.`2]) = e.`1.`2 => badE))
  /\ (forall u, u \in sec => u \in sv /\ oget sec.[u] = oget sv.[u]).

lemma einv_finv toks sv sec log ctr badE lft :
  einv toks sv sec log ctr badE lft => finv sv sec log badE.
proof. by rewrite /einv /finv => -[#] h1 h2 h3 *. qed.

lemma finv_rev sv sec log badE (u : int) (s : vec * row) :
  finv sv sec log badE => u \notin sv =>
  finv sv.[u <- s] sec.[u <- s] log (badE \/ popn s \in lpts log u).
proof.
rewrite /finv => -[h1 h3] hu; split.
- move=> e he; rewrite mem_set get_setE; case: (e.`2 = u) => [heq | hne] /=.
  + by move=> hp; right; rewrite hp -heq; apply lpts_mem.
  by case: (h1 e he) => [hn | hb]; [left | right => /hb ->].
move=> w; rewrite !mem_set !get_setE; case: (w = u) => [-> /= | hne /= hw] //.
by have [hs hv] := h3 w hw; rewrite hs hv.
qed.

lemma einv_ph1 toks sv sec log ctr badE lft :
  einv toks sv sec log ctr badE lft =>
  forall i, 0 <= i < size (filter (fun u => (oget toks.[u]).`tk_phase = 1) (elems (fdom toks))) =>
    nth 0 (filter (fun u => (oget toks.[u]).`tk_phase = 1) (elems (fdom toks))) i \notin sv.
proof.
rewrite /einv => -[#] h1 h2 _ _ _ _ i hi.
have := mem_nth 0 (filter (fun u => (oget toks.[u]).`tk_phase = 1) (elems (fdom toks))) i hi.
by rewrite List.mem_filter -memE mem_fdom => -[/= hp hu]; apply h2.
qed.

lemma finv_ept sv sec log badE : finv sv sec log badE => eptof log sec => badE.
proof.
rewrite /finv /eptof hasP => -[h1 h3] [e [he /= [hs hp]]].
have [hsv heq] := h3 _ hs.
by case: (h1 e he) => [hn | hb]; [move: hn; rewrite hsv | apply hb; rewrite -heq].
qed.

section B1c.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -Fz, -Bd, -Lg1, -Bx, -H0H.QRO, -H0C.QRO,
                         -H1O.QRO, -HCO.QRO, -H0H.LC, -H0H.CQ}.

(* The instrumentation does not change the lazy replay *)
lemma bbx_lef &m :
  Pr[H0H.LCG(BBX(A)).main(true) @ &m : Lg1.ept] = Pr[LEf(A).main() @ &m : Lg1.ept].
proof.
byequiv => //; proc.
inline BBX(A, H0H.LC).main GameX(A, H0H.LC).run.
wp.
while (={k, us, S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt,
          glob Fz, glob Bd, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H1O.QRO,
          glob HCO.QRO, glob Lg1}).
+ by inline *; sim.
wp.
call (_ : ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt,
            glob Fz, glob Bd, glob H0H.LC, glob H0H.QRO, glob H0H.CQ, glob H0C.QRO, glob H1O.QRO,
            glob HCO.QRO, glob Lg1}).
+ by proc; inline *; sim.
+ by proc; inline *; sim.
+ by proc; inline *; sim.
+ by proc; inline *; sim.
+ by proc; inline *; sim.
+ by proc; inline *; sim.
by auto; call (_ : true); inline *; auto.
qed.

(* In the instrumented run, a logged opening point at the end raised the flag *)
lemma lef_ept : hoare [LEf(A).main : true ==> Lg1.ept => Bx.badE].
proof.
proc.
wp.
while (finv H0H.LC.sv Lg1.sec Lg1.log Bx.badE
       /\ us = filter (fun u => (oget S.toks.[u]).`tk_phase = 1) (elems (fdom S.toks))
       /\ (forall i, k <= i < size us => nth 0 us i \notin H0H.LC.sv) /\ uniq us /\ 0 <= k).
+ inline *; sp; if; last by auto => /> /#.
  auto => /> &h hf hk hu hk0 hk1 hsv s0 _; split; first by rewrite get_set_sameE /=; apply finv_rev.
  split; last smt().
  move=> i hi0 hi1; rewrite mem_set negb_or; split; first by apply hk; smt().
  apply/negP => heq.
  have h1 := index_uniq 0 i _ _ hu; first smt().
  have h2 := index_uniq 0 k{h} _ _ hu; first smt().
  smt().
wp.
call (_ : einv S.toks H0H.LC.sv Lg1.sec Lg1.log S.ctr Bx.badE H0H.LC.lft).
+ exact o1_e.
+ exact o2_e.
+ exact o3_e.
+ exact h0_e.
+ exact h1_e.
+ exact hc_e.
auto; call (_ : true); inline *; auto => /> *;
  (split; [by rewrite /einv; smt(mem_empty) |
   move=> _ badE log sec ctr toks sv hi; split;
     [ split; [exact (einv_finv _ _ _ _ _ _ _ hi) |
               split; [move=> i hi0 hi1; apply (einv_ph1 _ _ _ _ _ _ _ hi); split => // |
                       by apply filter_uniq; apply uniq_elems]]
     | move=> badE0 sec0 sv0 k _ hf _ _ _; exact (finv_ept _ _ _ _ hf) ]]).
qed.

end section B1c.
