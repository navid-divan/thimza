require import AllCore Int List Distr DList FMap FSet Real RealExp Finite StdOrder StdBigop.
require import Params Types BigOps Sharing ShamirLagrange Masking Corruption.
require import Protocol Notions Privacy Extract FinEnum ChainBase ChainGame ChainCol ChainSim.
require import ChainDead ChainLazy ChainFlag ChainGA ChainB1a.
import RqVec RqVec.Vector RqVec.Vector.ZModule RqRow.Vector RqRow.Vector.ZModule.

(* ---------- the first flag with eager commitments: a collision of H0 ----------

   With eager commitments every first message is the value of H0 at the opening point of its
   token.  An accepted honest check that raises the first flag, at a point other than the
   opening point of an inconsistent token with that first message, is a collision of H0; at the
   opening point itself the token is unopened and the check is logged (Ept). *)

module Lc0 = {
  var got : bool
  var x1  : h0in
  var x2  : h0in
}.

(* The opening point of a token *)
op [opaque] opt (toks : (int, token) fmap) (sv : (int, vec * row) fmap) (t : row) (w : int) : h0in =
  (((t, (oget toks.[w]).`tk_msg), toidx (oget toks.[w]).`tk_i), popn (oget sv.[w])).

(* An inconsistent token holding the first message whose opening point is not the check point *)
op [opaque] cwit (toks : (int, token) fmap) (sv : (int, vec * row) fmap) (t : row) (j : int) (mu : msg)
        (c : cmt) (x : h0in) (w : int) : bool =
  cmtok toks j c w
  /\ ((oget toks.[w]).`tk_phase = 1 \/ (oget toks.[w]).`tk_msg <> mu \/ (oget toks.[w]).`tk_wbar <> x.`2)
  /\ x <> opt toks sv t w.

(* Eager commitments over a given oracle for H0 *)
module LCE (H : H0H.QRO_i) : H0H.LC_i = {
  proc h(x : h0key * row) : cmt = {
    var r;
    r <@ H.h(x);
    return r;
  }

  proc commit(u : int, k : h0key) : cmt = {
    var r, s;
    s <@ H0H.LC.gsec(u);
    r <@ H.h((k, popn s));
    return r;
  }

  proc reveal = H0H.LC.reveal
}.

module BXOC (O : H0H.LC_i) : SOr = {
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
    var out, tok, d, k, okk, y, c, z, mkh, mkc, j, v, ys, f, w;
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
            if (!(nth 0 T k \in S.cs) /\ y = nth witness cs k /\ !Lc0.got) {
              w <- choiceb (fun w => cwit S.toks H0H.LC.sv S.t (nth 0 T k) tok.`tk_msg (nth witness cs k)
                                          (((S.t, tok.`tk_msg), toidx (nth 0 T k)), nth witness ws k) w) 0;
              if (cwit S.toks H0H.LC.sv S.t (nth 0 T k) tok.`tk_msg (nth witness cs k)
                       (((S.t, tok.`tk_msg), toidx (nth 0 T k)), nth witness ws k) w) {
                Lc0.got <- true;
                Lc0.x1 <- (((S.t, tok.`tk_msg), toidx (nth 0 T k)), nth witness ws k);
                Lc0.x2 <- opt S.toks H0H.LC.sv S.t w;
              }
            }
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

module GameXC (A : Adv) (O : H0H.LC_i) = {
  proc run() : bool = {
    var mu, sg, ok, sks, sds;
    S.cs <@ A(CntH(HOL(O)), CntO(BXOC(O))).corrupt();
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
    (mu, sg) <@ A(CntH(HOL(O)), CntO(BXOC(O))).forge(S.t, sks, sds);
    ok <- verify (hcof HCO.QRO.fh) S.t mu sg /\ admc S.cs;
    return win4 S.cs S.lo mu ok;
  }
}.

module BBXC (A : Adv) (O : H0H.LC_i) = {
  proc main() : bool = {
    var b, us, k;
    H0C.QRO.init();
    H1O.QRO.init();
    HCO.QRO.init();
    Lg1.log <- [];
    Lg1.sec <- empty;
    Lg1.ept <- false;
    b <@ GameXC(A, O).run();
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

module BCol (A : Adv) (H : H0H.QRO_i) = {
  proc main() : h0in * h0in = {
    var b;
    H0H.LC.sv <- empty;
    H0H.LC.rv <- [];
    H0H.LC.fv <- empty;
    H0H.LC.lft <- false;
    Lc0.got <- false;
    Lc0.x1 <- witness;
    Lc0.x2 <- witness;
    b <@ BBXC(A, LCE(H)).main();
    return (Lc0.x1, Lc0.x2);
  }
}.

(* The eager run: first messages are H0 at the opening points, opened tokens show their
   nonce, recorded nonces are the nonces, logged tokens exist, a recorded pair collides, and
   the first flag comes with a recorded pair or a logged opening point *)
op [opaque] cinv1 (toks : (int, token) fmap) (sv : (int, vec * row) fmap) (sec : (int, vec * row) fmap)
                  (log : (h0in * int) list) (t : row) (fh : h0in -> cmt) (b1 got : bool) (x1 x2 : h0in) : bool =
  (forall u, u \in toks => u \in sv /\ (oget toks.[u]).`tk_cmt = fh (opt toks sv t u))
  /\ (forall u, u \in toks => (oget toks.[u]).`tk_phase <> 1 =>
        (oget toks.[u]).`tk_wbar = popn (oget sv.[u]) /\ u \in sec)
  /\ (forall u, u \in sec => u \in sv /\ oget sec.[u] = oget sv.[u])
  /\ (forall (e : h0in * int), e \in log => e.`2 \in toks)
  /\ (got => x1 <> x2 /\ fh x1 = fh x2)
  /\ (b1 => got \/ exists (e : h0in * int), e \in log /\ popn (oget sv.[e.`2]) = e.`1.`2)
  /\ (forall u, u \in toks => (oget toks.[u]).`tk_phase = 2 => inrange (oget toks.[u]).`tk_T).

lemma h0_c1 :
  hoare [CntH(HOL(LCE(H0H.CQ))).h0 :
    cinv1 S.toks H0H.LC.sv Lg1.sec Lg1.log S.t H0H.QRO.fh Bd.b1 Lc0.got Lc0.x1 Lc0.x2 ==>
    cinv1 S.toks H0H.LC.sv Lg1.sec Lg1.log S.t H0H.QRO.fh Bd.b1 Lc0.got Lc0.x1 Lc0.x2].
proof. by proc; inline *; auto. qed.

lemma h1_c1 :
  hoare [CntH(HOL(LCE(H0H.CQ))).h1 :
    cinv1 S.toks H0H.LC.sv Lg1.sec Lg1.log S.t H0H.QRO.fh Bd.b1 Lc0.got Lc0.x1 Lc0.x2 ==>
    cinv1 S.toks H0H.LC.sv Lg1.sec Lg1.log S.t H0H.QRO.fh Bd.b1 Lc0.got Lc0.x1 Lc0.x2].
proof. by proc; inline *; auto. qed.

lemma hc_c1 :
  hoare [CntH(HOL(LCE(H0H.CQ))).hc :
    cinv1 S.toks H0H.LC.sv Lg1.sec Lg1.log S.t H0H.QRO.fh Bd.b1 Lc0.got Lc0.x1 Lc0.x2 ==>
    cinv1 S.toks H0H.LC.sv Lg1.sec Lg1.log S.t H0H.QRO.fh Bd.b1 Lc0.got Lc0.x1 Lc0.x2].
proof. by proc; inline *; auto. qed.

lemma o1_c1 :
  hoare [CntO(BXOC(LCE(H0H.CQ))).o1 :
    cinv1 S.toks H0H.LC.sv Lg1.sec Lg1.log S.t H0H.QRO.fh Bd.b1 Lc0.got Lc0.x1 Lc0.x2 ==>
    cinv1 S.toks H0H.LC.sv Lg1.sec Lg1.log S.t H0H.QRO.fh Bd.b1 Lc0.got Lc0.x1 Lc0.x2].
proof.
proc; inline BXOC(LCE(H0H.CQ)).o1; sp; if; last by auto.
inline *; sp; if.
+ auto => /> &h; rewrite /cinv1 /opt => -[#] h1 h2 h3 h4 h5 h6 h7 hi1 hi2 hic hsv s0 _ /=.
  do !split.
  - move=> u; rewrite !mem_set !get_setE; case: (u = S.ctr{h}) => [-> /= | hne /= hu]; first done.
    by have [hs hc] := h1 u hu; rewrite hs /= hc; smt(get_setE).
  - move=> u; rewrite !mem_set !get_setE; case: (u = S.ctr{h}) => [-> /= | hne /= hu hph] //.
    have [hw hsc] := h2 u hu hph; rewrite hw hsc /=.
    have [hs _] := h1 u hu; smt(get_setE).
  - by move=> u hu; have [hs he] := h3 u hu; rewrite mem_set hs get_setE; smt().
  - by move=> e he; rewrite mem_set; left; apply h4.
  - exact h5.
  - move=> hb; case: (h6 hb) => [-> // | [e [he hp]]]; right; exists e; split => //.
    have [hs _] := h1 e.`2 (h4 e he); smt(get_setE).
  move=> u; rewrite !mem_set !get_setE; case: (u = S.ctr{h}) => [-> /= | hne /= hu hph] //.
  exact (h7 u hu hph).
auto => /> &h; rewrite /cinv1 /opt => -[#] h1 h2 h3 h4 h5 h6 h7 hi1 hi2 hic hsv /=.
do !split.
- move=> u; rewrite !mem_set !get_setE; case: (u = S.ctr{h}) => [-> /= | hne /= hu]; first done.
  exact (h1 u hu).
- move=> u; rewrite !mem_set !get_setE; case: (u = S.ctr{h}) => [-> /= | hne /= hu hph] //.
  exact (h2 u hu hph).
- exact h3.
- by move=> e he; rewrite mem_set; left; apply h4.
- exact h5.
- exact h6.
move=> u; rewrite !mem_set !get_setE; case: (u = S.ctr{h}) => [-> /= | hne /= hu hph] //.
exact (h7 u hu hph).
qed.

lemma o2_c1 :
  hoare [CntO(BXOC(LCE(H0H.CQ))).o2 :
    cinv1 S.toks H0H.LC.sv Lg1.sec Lg1.log S.t H0H.QRO.fh Bd.b1 Lc0.got Lc0.x1 Lc0.x2 ==>
    cinv1 S.toks H0H.LC.sv Lg1.sec Lg1.log S.t H0H.QRO.fh Bd.b1 Lc0.got Lc0.x1 Lc0.x2].
proof.
proc; inline BXOC(LCE(H0H.CQ)).o2; sp; if; last by auto.
sp; if; last by auto.
inline *; sp; if.
+ by auto => /> &h; rewrite /cinv1 => -[#] h1 *; smt().
auto => /> &h; rewrite /cinv1 /opt => -[#] h1 h2 h3 h4 h5 h6 h7 hu hph huq hsz hin hiT hcs hown hsv /=.
do !split.
- move=> w; rewrite !mem_set !get_setE; case: (w = u{h}) => [-> /= | hne /= hu'] //; first smt().
  exact (h1 w hu').
- move=> w; rewrite !mem_set !get_setE; case: (w = u{h}) => [-> /= | hne /= hu' hph'] //.
  by have [hw hs] := h2 w hu' hph'; rewrite hw hs.
- move=> w; rewrite mem_set get_setE; case: (w = u{h}) => [-> /= | hne /= hu']; first smt().
  exact (h3 w hu').
- by move=> e he; rewrite mem_set; left; apply h4.
- exact h5.
- exact h6.
move=> w; rewrite !mem_set !get_setE; case: (w = u{h}) => [-> /= | hne /= hu' hph'] //.
exact (h7 w hu' hph').
qed.

(* One honest or corrupt check of the eager run *)
lemma c1_step toks sv sec log t fh b1 got x1 x2 (C : corrset) (mu : msg) (j : int) (c : cmt)
              (w0 : row) (y : cmt) :
  cinv1 toks sv sec log t fh b1 got x1 x2 => 1 <= j <= nmax =>
  (!(j \in C) => y = fh (((t, mu), toidx j), w0)) =>
  cinv1 toks sv sec
    (if !(j \in C)
     then log ++ map (fun w => ((((t, mu), toidx j), w0), w))
                     (filter (fun w => (oget toks.[w]).`tk_phase = 1 /\ (oget toks.[w]).`tk_i = j)
                             (elems (fdom toks)))
     else log)
    t fh (b1 \/ (!(j \in C) /\ y = c /\ incons toks j mu c w0))
    (if !(j \in C) /\ y = c /\ !got
        /\ cwit toks sv t j mu c (((t, mu), toidx j), w0)
                (choiceb (fun w => cwit toks sv t j mu c (((t, mu), toidx j), w0) w) 0)
     then true else got)
    (if !(j \in C) /\ y = c /\ !got
        /\ cwit toks sv t j mu c (((t, mu), toidx j), w0)
                (choiceb (fun w => cwit toks sv t j mu c (((t, mu), toidx j), w0) w) 0)
     then (((t, mu), toidx j), w0) else x1)
    (if !(j \in C) /\ y = c /\ !got
        /\ cwit toks sv t j mu c (((t, mu), toidx j), w0)
                (choiceb (fun w => cwit toks sv t j mu c (((t, mu), toidx j), w0) w) 0)
     then opt toks sv t (choiceb (fun w => cwit toks sv t j mu c (((t, mu), toidx j), w0) w) 0)
     else x2).
proof.
rewrite /cinv1 => -[#] h1 h2 h3 h4 h5 h6 h7 hj hy.
pose x := (((t, mu), toidx j), w0).
pose W := choiceb (fun w => cwit toks sv t j mu c x w) 0.
do !split => //.
- move=> e; case: (j \in C) => hjC /=; first exact (h4 e).
  rewrite mem_cat => -[he | /mapP [w [hw ->]]]; first exact (h4 e he).
  by move: hw; rewrite List.mem_filter -memE mem_fdom => -[_ ->].
- case: (!(j \in C) /\ y = c /\ !got /\ cwit toks sv t j mu c x W) => hr /=; last exact h5.
  have [hjC [hyc [hng hcw0]]] := hr.
  move: hcw0; rewrite /cwit /cmtok => -[[hW [hWi hWc]] [_ hne]].
  split; first exact hne.
  have [_ hc] := h1 W hW.
  by rewrite -hy // hyc -hWc hc.
move=> hb.
case: (b1) => hb1.
- case: (h6 hb1) => [hg | [e [he hp]]].
  + by left; case: (_ /\ _) => //=; rewrite hg.
  right; exists e; split => //.
  by case: (j \in C) => //= _; rewrite mem_cat he.
move: hb; rewrite hb1 /= => -[hjC [hyc [u0 [[hu0 [hu0i hu0c]] hinc]]]].
case: (x = opt toks sv t u0) => hx.
- right; exists (x, u0); split; last first.
  + by move: hx; rewrite /opt /x => /= -[_ ->].
  rewrite hjC /= mem_cat; right; apply/mapP; exists u0; split => //.
  rewrite List.mem_filter /= -memE mem_fdom hu0 hu0i /=.
  case: (hinc) => [-> // | [hm | hw]].
  + by move: hx; rewrite /opt /x /= => -[[hm' _] _]; move: hm; rewrite hm'.
  case: ((oget toks.[u0]).`tk_phase = 1) => // hph.
  have [hwb _] := h2 u0 hu0 hph.
  by move: hx hw; rewrite /opt /x /= => -[_ ->]; rewrite hwb.
have hcw : cwit toks sv t j mu c x u0.
+ by rewrite /cwit /cmtok hu0 hu0i hu0c /= hx /=; move: hinc; rewrite /x.
have hW : cwit toks sv t j mu c x W.
+ by rewrite /W; apply (choicebP (fun w => cwit toks sv t j mu c x w) 0); exists u0.
by left; case: (got) => hg //=; rewrite hjC hyc /= hW.
qed.

lemma erase_flds1 (tk : token) :
  (erase tk).`tk_i = tk.`tk_i /\ (erase tk).`tk_msg = tk.`tk_msg /\ (erase tk).`tk_wbar = tk.`tk_wbar
  /\ (erase tk).`tk_cmt = tk.`tk_cmt /\ (erase tk).`tk_T = tk.`tk_T /\ (erase tk).`tk_phase = 0.
proof. by rewrite /erase. qed.

lemma c1_erase toks sv sec log t fh b1 got x1 x2 (u : int) :
  cinv1 toks sv sec log t fh b1 got x1 x2 => u \in toks => (oget toks.[u]).`tk_phase = 2 =>
  cinv1 toks.[u <- erase (oget toks.[u])] sv sec log t fh b1 got x1 x2.
proof.
rewrite /cinv1 /opt => -[#] h1 h2 h3 h4 h5 h6 h7 hu hph.
have [#] e1 e2 e3 e4 e5 e6 := erase_flds1 (oget toks.[u]).
do !split => //.
- move=> w; rewrite mem_set get_setE; case: (w = u) => [-> /= | hne /= hw]; last exact (h1 w hw).
  by rewrite e1 e2 e4; exact (h1 u hu).
- move=> w; rewrite mem_set get_setE; case: (w = u) => [-> /= | hne /= hw hp]; last exact (h2 w hw hp).
  by move=> _; rewrite e3; apply (h2 u hu); rewrite hph.
- by move=> e he; rewrite mem_set; left; apply h4.
move=> w; rewrite mem_set get_setE; case: (w = u) => [-> /= | hne /= hw hp]; last exact (h7 w hw hp).
by rewrite e6.
qed.

lemma h0any_c (x0 : h0in) :
  hoare [SOA(LCE(H0H.CQ)).h0any : x = x0 ==> !(PIdx.val x0.`1.`2 \in S.cs) => res = H0H.QRO.fh x0].
proof. by proc; inline *; auto. qed.

lemma o3_c1 :
  hoare [CntO(BXOC(LCE(H0H.CQ))).o3 :
    cinv1 S.toks H0H.LC.sv Lg1.sec Lg1.log S.t H0H.QRO.fh Bd.b1 Lc0.got Lc0.x1 Lc0.x2 ==>
    cinv1 S.toks H0H.LC.sv Lg1.sec Lg1.log S.t H0H.QRO.fh Bd.b1 Lc0.got Lc0.x1 Lc0.x2].
proof.
proc; inline BXOC(LCE(H0H.CQ)).o3; sp; if; last by auto.
sp; if; last by auto.
sp; if; last by auto.
seq 3 : (cinv1 S.toks H0H.LC.sv Lg1.sec Lg1.log S.t H0H.QRO.fh Bd.b1 Lc0.got Lc0.x1 Lc0.x2
         /\ u0 \in S.toks /\ tok = oget S.toks.[u0] /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T /\ 0 <= k).
+ by auto.
seq 1 : (cinv1 S.toks H0H.LC.sv Lg1.sec Lg1.log S.t H0H.QRO.fh Bd.b1 Lc0.got Lc0.x1 Lc0.x2
         /\ u0 \in S.toks /\ tok = oget S.toks.[u0] /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T).
+ while (cinv1 S.toks H0H.LC.sv Lg1.sec Lg1.log S.t H0H.QRO.fh Bd.b1 Lc0.got Lc0.x1 Lc0.x2
         /\ u0 \in S.toks /\ tok = oget S.toks.[u0] /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T /\ 0 <= k);
    last by auto.
  wp; ecall (h0any_c (((S.t, tok.`tk_msg), toidx (nth 0 T0 k)), nth witness ws0 k)); auto.
  move=> &h [[hc [hu [htok [hph [hT hk0]]]]] hk].
  have hin : 1 <= nth 0 T0{h} k{h} <= nmax.
  + move: hc; rewrite /cinv1 => -[#] _ _ _ _ _ _ h7.
    have := h7 u0{h} hu _; first by rewrite -htok.
    rewrite -htok -hT /inrange => /allP; apply; apply mem_nth; smt(size_ge0).
  have htx := toidxK _ hin.
  case: (nth 0 T0{h} k{h} \in S.cs{h}) => hjC /=; move=> y hy.
  + have := c1_step _ _ _ _ _ _ _ _ _ _ S.cs{h} tok{h}.`tk_msg (nth 0 T0{h} k{h})
              (nth witness cs0{h} k{h}) (nth witness ws0{h} k{h}) y hc hin _; first by rewrite hjC.
    by rewrite hjC /= => -> /#.
  have := c1_step _ _ _ _ _ _ _ _ _ _ S.cs{h} tok{h}.`tk_msg (nth 0 T0{h} k{h})
            (nth witness cs0{h} k{h}) (nth witness ws0{h} k{h}) y hc hin _.
  + by move=> _; apply hy; rewrite htx hjC.
  rewrite hjC /= => hres.
  case: (y = nth witness cs0{h} k{h} /\ !Lc0.got{h}) => hq /=.
  + have [hy1 hg] := hq.
    case: (cwit S.toks{h} H0H.LC.sv{h} S.t{h} (nth 0 T0{h} k{h}) tok{h}.`tk_msg (nth witness cs0{h} k{h})
             (((S.t{h}, tok{h}.`tk_msg), toidx (nth 0 T0{h} k{h})), nth witness ws0{h} k{h})
             (choiceb (cwit S.toks{h} H0H.LC.sv{h} S.t{h} (nth 0 T0{h} k{h}) tok{h}.`tk_msg
                        (nth witness cs0{h} k{h})
                        (((S.t{h}, tok{h}.`tk_msg), toidx (nth 0 T0{h} k{h})), nth witness ws0{h} k{h})) 0))
           => hcw /=.
    - by move: hres; rewrite hy1 hg hcw /= => -> /#.
    by move: hres; rewrite hy1 hg hcw /= => -> /#.
  by move: hres; smt().
if; last by auto.
seq 6 : (cinv1 S.toks H0H.LC.sv Lg1.sec Lg1.log S.t H0H.QRO.fh Bd.b1 Lc0.got Lc0.x1 Lc0.x2
         /\ u0 \in S.toks /\ tok = oget S.toks.[u0] /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T).
+ by while (cinv1 S.toks H0H.LC.sv Lg1.sec Lg1.log S.t H0H.QRO.fh Bd.b1 Lc0.got Lc0.x1 Lc0.x2
            /\ u0 \in S.toks /\ tok = oget S.toks.[u0] /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T); auto.
by sp; if; [auto | if; auto] => /> &h hc hu hph *; apply c1_erase.
qed.

(* The eager commitments over the collision oracle are the eager commitments *)
equiv h0any_e :
  SOA(H0H.LC).h0any ~ SOA(LCE(H0H.CQ)).h0any : ={x} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1}.
proof.
proc; sp; if => //; first by auto.
inline *; sp; rcondf{1} 1; first by auto => /> /#.
by auto.
qed.

equiv h0_e1 :
  CntH(HOL(H0H.LC)).h0 ~ CntH(HOL(LCE(H0H.CQ))).h0 :
  ={x} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1} /\ cinv1 S.toks{2} H0H.LC.sv{2} Lg1.sec{2} Lg1.log{2} S.t{2} H0H.QRO.fh{2} Bd.b1{2} Lc0.got{2}
        Lc0.x1{2} Lc0.x2{2} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1} /\ cinv1 S.toks{2} H0H.LC.sv{2} Lg1.sec{2} Lg1.log{2} S.t{2} H0H.QRO.fh{2} Bd.b1{2} Lc0.got{2}
        Lc0.x1{2} Lc0.x2{2}.
proof.
conseq (_ : ={x} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1}) _ h0_c1 => //.
proc; inline HOL(H0H.LC).h0 HOL(LCE(H0H.CQ)).h0; sp; if => //; first by auto.
inline *; sp; rcondf{1} 1; first by auto => /> /#.
by auto.
qed.

equiv h1_e1 :
  CntH(HOL(H0H.LC)).h1 ~ CntH(HOL(LCE(H0H.CQ))).h1 :
  ={x} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1} /\ cinv1 S.toks{2} H0H.LC.sv{2} Lg1.sec{2} Lg1.log{2} S.t{2} H0H.QRO.fh{2} Bd.b1{2} Lc0.got{2}
        Lc0.x1{2} Lc0.x2{2} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1} /\ cinv1 S.toks{2} H0H.LC.sv{2} Lg1.sec{2} Lg1.log{2} S.t{2} H0H.QRO.fh{2} Bd.b1{2} Lc0.got{2}
        Lc0.x1{2} Lc0.x2{2}.
proof.
conseq (_ : ={x} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1}) _ h1_c1 => //.
by proc; inline *; auto.
qed.

equiv hc_e1 :
  CntH(HOL(H0H.LC)).hc ~ CntH(HOL(LCE(H0H.CQ))).hc :
  ={x} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1} /\ cinv1 S.toks{2} H0H.LC.sv{2} Lg1.sec{2} Lg1.log{2} S.t{2} H0H.QRO.fh{2} Bd.b1{2} Lc0.got{2}
        Lc0.x1{2} Lc0.x2{2} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1} /\ cinv1 S.toks{2} H0H.LC.sv{2} Lg1.sec{2} Lg1.log{2} S.t{2} H0H.QRO.fh{2} Bd.b1{2} Lc0.got{2}
        Lc0.x1{2} Lc0.x2{2}.
proof.
conseq (_ : ={x} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1}) _ hc_c1 => //.
by proc; inline *; auto.
qed.

equiv o1_e1 :
  CntO(BXO(H0H.LC)).o1 ~ CntO(BXOC(LCE(H0H.CQ))).o1 :
  ={i, mu} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1} /\ cinv1 S.toks{2} H0H.LC.sv{2} Lg1.sec{2} Lg1.log{2} S.t{2} H0H.QRO.fh{2} Bd.b1{2} Lc0.got{2}
        Lc0.x1{2} Lc0.x2{2} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1} /\ cinv1 S.toks{2} H0H.LC.sv{2} Lg1.sec{2} Lg1.log{2} S.t{2} H0H.QRO.fh{2} Bd.b1{2} Lc0.got{2}
        Lc0.x1{2} Lc0.x2{2}.
proof.
conseq (_ : ={i, mu} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1}) _ o1_c1 => //.
proc; inline BXO(H0H.LC).o1 BXOC(LCE(H0H.CQ)).o1; sp; if => //; last by auto.
inline H0H.LC.commit LCE(H0H.CQ).commit; sp; rcondf{1} 1; first by auto => /> /#.
inline *; sp; if => //; auto.
qed.

equiv o2_e1 :
  CntO(BXO(H0H.LC)).o2 ~ CntO(BXOC(LCE(H0H.CQ))).o2 :
  ={u, T, cs} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1} /\ cinv1 S.toks{2} H0H.LC.sv{2} Lg1.sec{2} Lg1.log{2} S.t{2} H0H.QRO.fh{2} Bd.b1{2} Lc0.got{2}
        Lc0.x1{2} Lc0.x2{2} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1} /\ cinv1 S.toks{2} H0H.LC.sv{2} Lg1.sec{2} Lg1.log{2} S.t{2} H0H.QRO.fh{2} Bd.b1{2} Lc0.got{2}
        Lc0.x1{2} Lc0.x2{2}.
proof.
conseq (_ : ={u, T, cs} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1}) _ o2_c1 => //.
proc; inline BXO(H0H.LC).o2 BXOC(LCE(H0H.CQ)).o2; sp; if => //; last by auto.
sp; if => //; last by auto.
by inline *; sp; if => //; auto.
qed.

equiv o3_e1 :
  CntO(BXO(H0H.LC)).o3 ~ CntO(BXOC(LCE(H0H.CQ))).o3 :
  ={u, T, cs, ws} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1} /\ cinv1 S.toks{2} H0H.LC.sv{2} Lg1.sec{2} Lg1.log{2} S.t{2} H0H.QRO.fh{2} Bd.b1{2} Lc0.got{2}
        Lc0.x1{2} Lc0.x2{2} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1} /\ cinv1 S.toks{2} H0H.LC.sv{2} Lg1.sec{2} Lg1.log{2} S.t{2} H0H.QRO.fh{2} Bd.b1{2} Lc0.got{2}
        Lc0.x1{2} Lc0.x2{2}.
proof.
conseq (_ : ={u, T, cs, ws} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1} ==> ={res} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1}) _ o3_c1 => //.
proc; inline BXO(H0H.LC).o3 BXOC(LCE(H0H.CQ)).o3; sp; if => //; last by auto.
sp; if => //; last by auto.
sp; if => //; last by auto.
seq 3 3 : (={u0, T0, cs0, ws0, tok, d, out, okk, k} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1}); first by auto.
seq 1 1 : (={u0, T0, cs0, ws0, tok, d, out, okk, k} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1}).
+ while (={u0, T0, cs0, ws0, tok, d, out, okk, k} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1}); last by auto.
  wp; call h0any_e; auto.
if => //; last by auto.
seq 5 5 : (={u0, T0, cs0, ws0, tok, d, out, okk, k, c, ys, mkh, mkc} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1}); first by auto.
seq 1 1 : (={u0, T0, cs0, ws0, tok, d, out, okk, k, c, ys, mkh, mkc} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1}).
+ by while (={u0, T0, cs0, ws0, tok, d, out, okk, k, c, ys, mkh, mkc} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1}); auto.
seq 1 1 : (={u0, T0, cs0, ws0, tok, d, out, okk, k, c, ys, mkh, mkc, f} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1}); first by auto.
by if => //; [auto | if => //; auto].
qed.

(* A final reveal records the nonce of the token *)
lemma c1_rev toks sv sec log t fh b1 got x1 x2 (u : int) :
  cinv1 toks sv sec log t fh b1 got x1 x2 => u \in toks =>
  cinv1 toks sv sec.[u <- oget sv.[u]] log t fh b1 got x1 x2.
proof.
rewrite /cinv1 => -[#] h1 h2 h3 h4 h5 h6 h7 hu; do !split => //.
- by move=> w hw hp; have [hb hs] := h2 w hw hp; rewrite hb mem_set hs.
move=> w; rewrite mem_set get_setE; case: (w = u) => [-> /= | hne /= hw]; first by have [] := h1 u hu.
exact (h3 w hw).
qed.

(* At the end every token has its nonce recorded, and the first flag without a logged opening
   point comes with a collision *)
lemma fin_col toks sv sec log t fh b1 got x1 x2 :
  cinv1 toks sv sec log t fh b1 got x1 x2 => (forall u, u \in toks => u \in sec) =>
  b1 => !eptof log sec => x1 <> x2 /\ fh x1 = fh x2.
proof.
rewrite /cinv1 => -[#] h1 h2 h3 h4 h5 h6 h7 hall hb hne.
case: (h6 hb) => [hg | [e [he hp]]]; first exact (h5 hg).
have hs := hall _ (h4 e he).
have [_ heq] := h3 _ hs.
have hept : eptof log sec.
+ by rewrite /eptof hasP; exists e; rewrite he /= hs heq hp.
by move: hne; rewrite hept.
qed.

lemma c1_insv toks sv sec log t fh b1 got x1 x2 (u : int) :
  cinv1 toks sv sec log t fh b1 got x1 x2 => u \in toks => u \in sv.
proof. by rewrite /cinv1 => -[#] h1 _ _ _ _ _ _ hu; have [] := h1 u hu. qed.

lemma nth_us (P : int -> bool) (toks : (int, token) fmap) (k : int) :
  0 <= k < size (filter P (elems (fdom toks))) => nth 0 (filter P (elems (fdom toks))) k \in toks.
proof.
move=> hk; have := mem_nth 0 _ _ hk.
by rewrite List.mem_filter -memE mem_fdom => -[_ ->].
qed.

lemma all_sec toks sv sec log t fh b1 got x1 x2 :
  cinv1 toks sv sec log t fh b1 got x1 x2 =>
  (forall i, 0 <= i < size (filter (fun u => (oget toks.[u]).`tk_phase = 1) (elems (fdom toks))) =>
     nth 0 (filter (fun u => (oget toks.[u]).`tk_phase = 1) (elems (fdom toks))) i \in sec) =>
  forall u, u \in toks => u \in sec.
proof.
rewrite /cinv1 => -[#] h1 h2 h3 h4 h5 h6 h7 hall u hu.
case: ((oget toks.[u]).`tk_phase = 1) => hph; last by have [] := h2 u hu hph.
have hm : u \in filter (fun u => (oget toks.[u]).`tk_phase = 1) (elems (fdom toks)).
+ by rewrite List.mem_filter /= hph -memE mem_fdom.
have := hall (index u (filter (fun u => (oget toks.[u]).`tk_phase = 1) (elems (fdom toks)))) _.
+ by rewrite index_ge0 index_mem.
by rewrite nth_index.
qed.

(* The collision finder asks H0 at most qh0 + (1 + tthr) qsig times *)
op [opaque] qinv2 (n c0 cs : int) (toks : (int, token) fmap) : bool =
  0 <= cs /\ n <= c0 + (1 + tthr) * cs
  /\ (forall u, u \in toks => (oget toks.[u]).`tk_phase = 2 => size (oget toks.[u]).`tk_T = tthr).

lemma qinv2_mono n n' c0 cs toks : n' <= n => qinv2 n c0 cs toks => qinv2 n' c0 cs toks.
proof. by rewrite /qinv2; smt(). qed.

lemma h0any_q2 (n0 : int) :
  hoare [SOA(LCE(H0H.CQ)).h0any : H0H.CQ.n = n0 ==> H0H.CQ.n <= n0 + 1].
proof. by proc; inline *; auto => /> /#. qed.

lemma h0_q2 : hoare [CntH(HOL(LCE(H0H.CQ))).h0 : qinv2 H0H.CQ.n Cnt.c0 Cnt.cs S.toks ==> qinv2 H0H.CQ.n Cnt.c0 Cnt.cs S.toks].
proof. by proc; inline *; auto; rewrite /qinv2 => &h />; smt(thr_range). qed.

lemma h1_q2 : hoare [CntH(HOL(LCE(H0H.CQ))).h1 : qinv2 H0H.CQ.n Cnt.c0 Cnt.cs S.toks ==> qinv2 H0H.CQ.n Cnt.c0 Cnt.cs S.toks].
proof. by proc; inline *; auto. qed.

lemma hc_q2 : hoare [CntH(HOL(LCE(H0H.CQ))).hc : qinv2 H0H.CQ.n Cnt.c0 Cnt.cs S.toks ==> qinv2 H0H.CQ.n Cnt.c0 Cnt.cs S.toks].
proof. by proc; inline *; auto. qed.

lemma o1_q2 : hoare [CntO(BXOC(LCE(H0H.CQ))).o1 : qinv2 H0H.CQ.n Cnt.c0 Cnt.cs S.toks ==> qinv2 H0H.CQ.n Cnt.c0 Cnt.cs S.toks].
proof.
proc; inline BXOC(LCE(H0H.CQ)).o1; sp; if; last by auto; rewrite /qinv2 => &h />; smt(thr_range).
by inline *; sp; if; auto; rewrite /qinv2 => &h /> *; smt(mem_set get_setE thr_range).
qed.

lemma o2_q2 : hoare [CntO(BXOC(LCE(H0H.CQ))).o2 : qinv2 H0H.CQ.n Cnt.c0 Cnt.cs S.toks ==> qinv2 H0H.CQ.n Cnt.c0 Cnt.cs S.toks].
proof.
proc; inline BXOC(LCE(H0H.CQ)).o2; sp; if; last by auto; rewrite /qinv2 => &h />; smt(thr_range).
sp; if; last by auto; rewrite /qinv2 => &h />; smt(thr_range).
by inline *; sp; if; auto; rewrite /qinv2 => &h /> *; smt(mem_set get_setE thr_range).
qed.

lemma o3_q2 : hoare [CntO(BXOC(LCE(H0H.CQ))).o3 : qinv2 H0H.CQ.n Cnt.c0 Cnt.cs S.toks ==> qinv2 H0H.CQ.n Cnt.c0 Cnt.cs S.toks].
proof.
proc; inline BXOC(LCE(H0H.CQ)).o3; sp; if; last by auto; rewrite /qinv2 => &h />; smt(thr_range).
sp; if; last by auto; rewrite /qinv2 => &h />; smt(thr_range).
sp; if; last by auto; rewrite /qinv2 => &h />; smt(thr_range).
seq 3 : (qinv2 (H0H.CQ.n - k) Cnt.c0 (Cnt.cs - 1) S.toks /\ 0 <= k <= size T0 /\ size T0 = tthr
         /\ u0 \in S.toks /\ tok = oget S.toks.[u0] /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T).
+ by auto; rewrite /qinv2 => &h />; smt(thr_range).
seq 1 : (qinv2 (H0H.CQ.n - k) Cnt.c0 (Cnt.cs - 1) S.toks /\ 0 <= k <= size T0 /\ size T0 = tthr
         /\ u0 \in S.toks /\ tok = oget S.toks.[u0] /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T).
+ while (qinv2 (H0H.CQ.n - k) Cnt.c0 (Cnt.cs - 1) S.toks /\ 0 <= k <= size T0 /\ size T0 = tthr
         /\ u0 \in S.toks /\ tok = oget S.toks.[u0] /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T).
  - wp; ecall (h0any_q2 H0H.CQ.n); auto => /> &h hq hk0 hk1 hsz hu hph hk n hn.
    split; last smt().
    by apply (qinv2_mono (H0H.CQ.n{h} - k{h})); first smt().
  by auto => />.
if; last by auto; rewrite /qinv2 => &h /> /#.
seq 5 : (qinv2 (H0H.CQ.n - size T0) Cnt.c0 (Cnt.cs - 1) S.toks /\ size T0 = tthr
         /\ u0 \in S.toks /\ tok = oget S.toks.[u0] /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T).
+ auto => /> &h hq hk0 hk1 hsz hu hph _.
  by apply (qinv2_mono (H0H.CQ.n{h} - k{h})); first smt().
seq 1 : (qinv2 (H0H.CQ.n - size T0) Cnt.c0 (Cnt.cs - 1) S.toks /\ size T0 = tthr
         /\ u0 \in S.toks /\ tok = oget S.toks.[u0] /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T).
+ by while (qinv2 (H0H.CQ.n - size T0) Cnt.c0 (Cnt.cs - 1) S.toks /\ size T0 = tthr
         /\ u0 \in S.toks /\ tok = oget S.toks.[u0] /\ tok.`tk_phase = 2 /\ T0 = tok.`tk_T); auto.
by sp; if; [auto | if; auto] => /> &h; rewrite /qinv2 => *; smt(mem_set get_setE thr_range).
qed.

section B1b.

declare module A <: Adv {-S, -Cnt, -Lg, -MPR, -MPI, -Fz, -Bd, -Lg1, -Lc0, -H0H.QRO, -H0C.QRO,
                         -H1O.QRO, -HCO.QRO, -H0H.LC, -H0H.CQ}.

(* The first flag without a logged opening point gives a collision of H0 in the eager game *)
lemma bbx_col &m :
  Pr[H0H.LCG(BBX(A)).main(false) @ &m : res] <= Pr[H0H.Col(BCol(A)).main() @ &m : res].
proof.
byequiv => //; proc.
inline BCol(A, H0H.CQ).main BBX(A, H0H.LC).main BBXC(A, LCE(H0H.CQ)).main GameX(A, H0H.LC).run
       GameXC(A, LCE(H0H.CQ)).run.
wp.
while (={k, us} /\ ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1} /\ cinv1 S.toks{2} H0H.LC.sv{2} Lg1.sec{2} Lg1.log{2} S.t{2} H0H.QRO.fh{2} Bd.b1{2} Lc0.got{2}
        Lc0.x1{2} Lc0.x2{2}
       /\ us{2} = filter (fun u => (oget S.toks{2}.[u]).`tk_phase = 1) (elems (fdom S.toks{2}))
       /\ (forall i, 0 <= i < k{2} => nth 0 us{2} i \in Lg1.sec{2}) /\ 0 <= k{2}).
+ inline *; sp; if => //.
  + auto => /> &1 &2 *.
    smt(c1_insv nth_us).
  auto => /> &1 &2 *.
  split => _; (split; [apply c1_rev => //; apply nth_us; smt()
                      | split; [move=> i hi0 hi1; rewrite mem_set; smt() | smt()]]).
wp.
call (_ : ={S.cs, S.s, S.e, S.p, S.t, S.sdc, S.toks, S.req, S.ctr, S.lo, S.lr, glob Cnt, glob Fz, glob Bd,
        H0H.LC.sv, H0H.LC.rv, H0H.LC.fv, H0H.LC.lft, H0H.QRO.fh, glob H0C.QRO, glob H1O.QRO,
        glob HCO.QRO, glob Lg1} /\ !H0H.LC.lft{1} /\ cinv1 S.toks{2} H0H.LC.sv{2} Lg1.sec{2} Lg1.log{2} S.t{2} H0H.QRO.fh{2} Bd.b1{2} Lc0.got{2}
        Lc0.x1{2} Lc0.x2{2}).
+ exact o1_e1.
+ exact o2_e1.
+ exact o3_e1.
+ exact h0_e1.
+ exact h1_e1.
+ exact hc_e1.
auto; call (_ : true); inline *; auto => />.
move=> *; split; first by rewrite /cinv1; smt(mem_empty).
move=> hinit *; split; first smt().
move=> sec sv k hk _ hc hall hk0 hb hne.
apply (fin_col _ _ _ _ _ _ _ _ _ _ hc _ hb hne).
by apply (all_sec _ _ _ _ _ _ _ _ _ _ hc) => i hi; apply hall; smt().
qed.

declare axiom A_bnd (H <: HOr {-A, -Cnt}) (O <: SOr {-A, -Cnt}) :
  hoare [A(CntH(H), CntO(O)).forge : Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 ==>
         Cnt.c0 <= qh0 /\ Cnt.c1 <= qh1 /\ Cnt.cc <= qhc /\ Cnt.cs <= qsig].

local lemma forge_q2 :
  hoare [A(CntH(HOL(LCE(H0H.CQ))), CntO(BXOC(LCE(H0H.CQ)))).forge :
    qinv2 H0H.CQ.n Cnt.c0 Cnt.cs S.toks /\ Cnt.c0 = 0 /\ Cnt.c1 = 0 /\ Cnt.cc = 0 /\ Cnt.cs = 0 ==>
    qinv2 H0H.CQ.n Cnt.c0 Cnt.cs S.toks /\ Cnt.c0 <= qh0 /\ Cnt.cs <= qsig].
proof.
conseq (A_bnd (HOL(LCE(H0H.CQ))) (BXOC(LCE(H0H.CQ)))) (_ : qinv2 H0H.CQ.n Cnt.c0 Cnt.cs S.toks ==> qinv2 H0H.CQ.n Cnt.c0 Cnt.cs S.toks) => //.
proc (qinv2 H0H.CQ.n Cnt.c0 Cnt.cs S.toks) => //.
+ exact o1_q2.
+ exact o2_q2.
+ exact o3_q2.
+ exact h0_q2.
+ exact h1_q2.
+ exact hc_q2.
qed.

local lemma bcol_q : hoare [BCol(A, H0H.CQ).main : H0H.CQ.n = 0 ==> H0H.CQ.n <= qh0 + (1 + tthr) * qsig].
proof.
proc; inline BBXC(A, LCE(H0H.CQ)).main GameXC(A, LCE(H0H.CQ)).run.
wp.
while (H0H.CQ.n <= qh0 + (1 + tthr) * qsig); first by inline *; sp; if; auto.
wp; call forge_q2.
auto; call (_ : true); inline *; auto => /> *;
  (split; [by rewrite /qinv2; smt(mem_empty) |
           move=> _ c0 cs toks n; rewrite /qinv2 => -[#] h0 h1 _ hc0 hcs;
           have hm : (1 + tthr) * cs <= (1 + tthr) * qsig;
             [apply StdOrder.IntOrder.ler_wpmul2l; smt(thr_range) | smt()]]).
qed.

(* In the eager game, the first flag without a logged opening point is unlikely *)
lemma bbx_b1col &m :
  Pr[H0H.LCG(BBX(A)).main(false) @ &m : res]
  <= 27%r * (qh0 + (1 + tthr) * qsig + 2)%r ^ 3 * p_max dcmt.
proof.
apply (StdOrder.RealOrder.ler_trans _ _ _ (bbx_col &m)).
exact (H0H.pr_col (BCol(A)) &m (qh0 + (1 + tthr) * qsig) bcol_q).
qed.

end section B1b.
